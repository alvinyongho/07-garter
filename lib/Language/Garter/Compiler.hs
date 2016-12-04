{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

--------------------------------------------------------------------------------
-- | The entry point for the compiler: a function that takes a Text
--   representation of the source and returns a (Text) representation
--   of the assembly-program string representing the compiled version
--------------------------------------------------------------------------------

module Language.Garter.Compiler ( compiler, compile, compileEnv, countVars, freeVars, typeTag, typeMask ) where

import           Prelude                  hiding (compare)
import           Control.Arrow            ((>>>))
import           Data.Maybe
import           Data.Bits                       (shift)
import qualified Data.Set                as S
-- import           Language.Garter.Utils
import           Language.Garter.Types      hiding (Tag)
import           Language.Garter.Parser     (parse)
import           Language.Garter.Checker    (check, errUnboundVar)
import           Language.Garter.Normalizer (anormal)
import           Language.Garter.Asm        (asm)

--------------------------------------------------------------------------------
compiler :: FilePath -> Text -> Text
--------------------------------------------------------------------------------
compiler f = parse f >>> check >>> anormal >>> tag >>> compile >>> asm

--------------------------------------------------------------------------------
-- | The compilation (code generation) works with AST nodes labeled by @Tag@
--------------------------------------------------------------------------------
type Tag   = (SourceSpan, Int)
type AExp  = AnfExpr Tag
type IExp  = ImmExpr Tag
type ABind = Bind    Tag

instance Located Tag where
  sourceSpan = fst

instance Located a => Located (Expr a) where
  sourceSpan = sourceSpan . getLabel

--------------------------------------------------------------------------------
-- | @tag@ annotates each AST node with a distinct Int value
--------------------------------------------------------------------------------
tag :: AnfExpr SourceSpan -> AExp
--------------------------------------------------------------------------------
tag = label

--------------------------------------------------------------------------------
compile :: AExp -> [Instruction]
--------------------------------------------------------------------------------
compile e = funInstrs (countVars e) (compileEnv emptyEnv e)

-- | @funInstrs n body@ returns the instructions of `body` wrapped
--   with code that sets up the stack (by allocating space for n local vars)
--   and restores the callees stack prior to return.
funInstrs :: Int -> [Instruction] -> [Instruction]
funInstrs n instrs = funEntry n ++ instrs ++ funExit


funEntry :: Int -> [Instruction]
funEntry n = [ IPush (Reg EBP)                       -- save caller's ebp
             , IMov  (Reg EBP) (Reg ESP)             -- set callee's ebp
             , ISub  (Reg ESP) (Const (4 * n))       -- allocate n local-vars
             , IAnd  (Reg ESP) (HexConst 0xFFFFFFF0) -- MacOS stack alignment
             ]

funExit :: [Instruction]
funExit   = [ IMov (Reg ESP) (Reg EBP)
            , IPop (Reg EBP)
            , IRet ]

--------------------------------------------------------------------------------
-- | @countVars e@ returns the maximum stack-size needed to evaluate e,
--   which is the maximum number of let-binds in scope at any point in e.
--------------------------------------------------------------------------------
countVars :: AnfExpr a -> Int
--------------------------------------------------------------------------------
countVars (Let _ e b _)  = max (countVars e)  (1 + countVars b)
countVars (If v e1 e2 _) = maximum [countVars v, countVars e1, countVars e2]
countVars _              = 0

--------------------------------------------------------------------------------
freeVars :: Expr a -> [Id]
--------------------------------------------------------------------------------
freeVars e =
  S.toList (go e)
  where
    go :: Expr a -> S.Set Id
    go (Id x _)          = S.singleton(x)
    go (Number _ _)      = S.empty
    go (Boolean _ _)     = S.empty

    go (Prim1 _ v _)     = S.unions[ go v ]
    go (Prim2 _ v1 v2 _) = S.unions[ go v1, go v2 ]
    go (Tuple e1 e2 _)   = S.unions[ go e1, go e2 ]
    go (GetItem vE _ _)  = S.unions[ go vE ]

    go (If e e1 e2 _)    = S.unions[ go e, go e1, go e2 ]
    go (App e es _)      = S.unions(map go (e:es))
    go (Let x e1 e2 _)   = S.union (go e1) (S.delete (bindId x) (go e2))       -- Remove from the set from x e2
    go (Lam xs e _)      = S.difference (go e) (S.fromList (map bindId xs))
    go (Fun f _ xs e _)  = S.difference (go e) (S.fromList (map bindId (f:xs)))    -- add the function id to the list of other free vars


--------------------------------------------------------------------------------
compileEnv :: Env -> AExp -> [Instruction]
--------------------------------------------------------------------------------
compileEnv env v@(Number {})     = [ compileImm env v  ]

compileEnv env v@(Boolean {})    = [ compileImm env v  ]

compileEnv env v@(Id {})         = [ compileImm env v  ]

compileEnv env e@(Let {})        = is ++ compileEnv env' body
  where
    (env', is)                   = compileBinds env [] binds
    (binds, body)                = exprBinds e

compileEnv env (Prim1 o v l)     = compilePrim1 l env o v

compileEnv env (Prim2 o v1 v2 l) = compilePrim2 l env o v1 v2

compileEnv env (If v e1 e2 l)    = IMov (Reg EAX) (immArg env v)
                                 : ICmp (Reg EAX) (repr False)
                                 : branch l IJe i1s i2s
  where
    i1s                          = compileEnv env e1
    i2s                          = compileEnv env e2

compileEnv env (Tuple e1 e2 _)    = pairAlloc -- size 2 tuple
                                    -- ++ addSize env (2) -- add size to the first index
                                    -- ++ tupleCopy env [e1,e2] 1 -- add e1 to 1, e2 to 2 and onwards
                                    -- ++ addPad env ((2) + 1) -- final padding
                                    ++ pairCopy Zero  (immArg env e1)
                                    ++ pairCopy One   (immArg env e2)
                                    ++ setTag (Reg EAX) TTuple -- set that tag

compileEnv env (GetItem vE f _)   = [ IMov (Reg EBX) (immArg env vE) ] -- load pointer into eax
                                 ++ [ ISub (Reg EBX) (typeTag TTuple) ] -- remove tag bits to get address location
                                 ++ [ IMov (Reg EAX) (pairAddrField f) ]    -- get that field index
                                --  ++ [ ISar (Reg ECX) (Const 1)]  -- bit shift
                                --  ++ [ IAdd (Reg ECX) (Const 1) ] -- increment the index by one (cuz of size)
                                --  ++ [ IMov (Reg EAX) (Sized DWordPtr (RegIndex EBX ECX))] -- EAX = EAX + ECX * 4

compileEnv env (Lam xs e l)      =   IJmp   end             -- Why?
                                    : ILabel start            -- Function start
                                    : lambdaBody l ys (map bindId xs) e
                                   ++ ILabel end            -- Function end
                                    -- : lamTuple env l (length xs)   -- Compile fun-tuple into EAX
                                    : lamTupleWrite l arity start env ys
                                    where
                                      i = snd l
                                      ys    = freeVars (Lam xs e l)
                                      arity = length xs
                                      start = LamStart i
                                      end   = LamEnd   i

compileEnv env (Fun f t xs e l) =  IJmp   funEnd             -- Why?
                                    : ILabel funStart            -- Function start
                                    : funBody l f ys (map bindId xs) e    -- free variables, parameters
                                   ++ ILabel funEnd            -- Function end
                                    -- : lamTuple env l (length xs)   -- Compile fun-tuple into EAX
                                    : lamTupleWrite l arity funStart env ys
                                    where
                                      i = snd l
                                      ys    = freeVars (Fun f t xs e l)
                                      arity = length (xs)
                                      funStart = DefStart (bindId f) i
                                      funEnd   = DefEnd   (bindId f) i
compileEnv env (App vE vXs l)      = --assertType env vE TClosure
                                     -- assertArity env vE (length vXs)
                                       tupleReadRaw  (immArg env vE) (repr (1 :: Int))  -- load vE[1] into EAX
                                     ++ [IPush (param env vX) | vX <- reverse vXs]        -- push args
                                     ++ [IPush (param env vE)]                            -- push in that closure pointer
                                     ++ [ICall (Reg EAX)]                                 -- call EAX
                                     ++ [IAdd  (Reg ESP) (Const (4 * (n+1)))]                         -- pop  args
                                     where
                                       n = (length vXs)




-- pairAlloc :: Asm
pairAlloc
 = [ IMov (Reg EAX) (Reg ESI)   -- copy current "free address" `esi` into `eax`
   , IAdd (Reg ESI) (Const 8)   -- increment `esi` by 8
   ]


-- pairCopy :: Field -> Arg -> Asm
pairCopy fld a
 = [ IMov (Reg EBX)    a
   , IMov (pairAddrField fld) (Reg EBX)
   ]


pairAddrField :: Field -> Arg
pairAddrField fld = Sized DWordPtr (RegOffset (4 * fieldOffset fld) EAX)



fieldOffset :: Field -> Int
fieldOffset Zero  = 0
fieldOffset One = 1



tupleReadRaw vE vI =
    [ IMov (Reg EBX) vE ]
 ++ [ ISub (Reg EBX) (typeTag TClosure) ]
 ++ [ IMov (Reg ECX) vI ]
 ++ [ ISar (Reg ECX) (Const 1) ]
 ++ [ IAdd (Reg ECX) (Const 1) ] -- increment the index by one
 ++ [ IMov (Reg EAX) (Sized DWordPtr (RegIndex EBX ECX))] -- EAX = EAX + ECX * 4


-- lambdaBody :: [Id] -> [Id] -> AExp -> [Instruction]
lambdaBody l ys xs e = funInstrs maxStack
                       ( restore ys           -- restore free vars from closure-ptr
                      ++ compileEnv env e )   -- exec function-body as before
 where
   maxStack       = envMax env + countVars e  -- max stack size
   env            = fromListEnv bs
   bs             = zip xs  [-3,-4..]         -- put params    into env/stack
                 ++ zip ys  [1..]             -- put free-vars into env/stack



funBody l f ys xs e = funInstrs maxStack
                       ( restore ys           -- restore free vars from closure-ptr
                      ++ compileEnv env e )   -- exec function-body as before
 where
   maxStack       = envMax env + countVars e  -- max stack size
   env            = fromListEnv bs
   bs             =
                 [((bindId f), -2)]
                 ++ zip (xs)  [-3,-4..]         -- put params    into env/stack
                 ++ zip ys  [1..]             -- put free-vars into env/stack      --we also put the function id on the free variables stack
                 -- ++ [((bindId f), 2)]

restoreFun f ys  = concat [ copy i | (y, i) <- zip ys [1..]]
                     where
                       closPtr = RegOffset 8 EBP
                       copy i  = tupleReadRaw closPtr (repr (i+1))  -- copy tuple-fld for y into EAX...
                              ++ [ IMov (stackVar i) (Reg EAX) ]    -- ...write EAX into stackVar for y


restore ys  = concat [ copy i | (y, i) <- zip ys [1..]]
 where
   closPtr = RegOffset 8 EBP
   copy i  = tupleReadRaw closPtr (repr (i+1))  -- copy tuple-fld for y into EAX...
          ++ [ IMov (stackVar i) (Reg EAX) ]    -- ...write EAX into stackVar for y


-- compileDecl :: ADcl -> [Instruction]
compileDecl l xs e = compileBody env e
 where
   env                     = fromListEnv (zip (bindId <$> xs) [-2, -3..])

compileBody :: Env -> AExp -> [Instruction]
compileBody env e = funInstrs (countVars e) (compileEnv env e)


lamTupleWrite l arity start env ys
 =  tupleAlloc  (2 + length ys)                    -- alloc tuple 2 + |ys|
 ++ tupleWriteAdv 1 env ( repr arity                       -- fill arity
                : CodePtr start                    -- fill code-ptr
                : [immArg env (Id y l) | y <- ys] )  -- fill free-vars
 ++ [ IOr  (Reg EAX) (typeTag TClosure) ]          -- set the tag bits



funTupleWrite l f arity start env ys
 =  tupleAlloc  (2 + length ys)                    -- alloc tuple 2 + |ys|
 ++ tupleWriteAdv 1 env ( repr arity                       -- fill arity
                : CodePtr start                    -- fill code-ptr
                : [immArg env (Id y l) | y <- ys] )  -- fill free-vars
 ++ [ IOr  (Reg EAX) (typeTag TClosure) ]          -- set the tag bits





tupleWriteAdv i env instrs =
 addSize env (length instrs)
 ++ tupleAddToIndex i env instrs
 ++ addPad env ((length instrs) + 1)


tupleAddToIndex _ env [] = []
tupleAddToIndex i env (e:es)
 =  [IMov (Reg EBX) (e)]
 ++ [IMov (pairAddr i) (Reg EBX)]
 ++ tupleAddToIndex (i+1) env es
--
-- lamTuple :: Env -> Tag -> Arity -> [Instruction] -- example call lamda env l 123 (with 123 additinal parameters)
-- lamTuple env l arity
--   =  tupleAlloc  2                                  -- alloc tuple size = 2
--   ++ tupleWrites env l arity  -- fill in (code-ptr, arity)
--   ++ [ IOr  (Reg EAX) (typeTag TClosure) ]          -- set the tag bits
--
--
-- tupleWrites :: Env -> Tag -> Arity -> [Instruction]
-- tupleWrites env l arity =
-- -- [ILabel (LamStart i), repr arity]
--   addSize env 2     -- add the size to the first index [0]
--   ++[ IMov (Reg EBX) (repr arity)]
--   ++[ IMov (pairAddr 1) (Reg EBX)]
--   ++[ IMov (Reg EBX) (CodePtr codeptr)]   -- the first argument of the tuple
--   ++[ IMov (pairAddr 2) (Reg EBX)]
--   -- where i = snd l
--   ++ addPad env (3) -- THAT FINAL PADDING (We have to prevent accessing later but set it as 0?)
--   -- -- ++ setTag (Reg EAX) TTuple     -- the the tag of EAX to a TTuple
--   where
--     codeptr = (LamStart i)
--     i = snd l


tupleAlloc args =
   [ IMov (Reg EAX) (Reg ESI)   -- copy current "free address" `esi` into `eax`
   , IMov (Sized DWordPtr (RegOffset 0 EAX)) (repr args)
   , IAdd (Reg ESI) (Const size)   -- increment `esi` by 8
   ]
   where
     size = 4 * roundToEven(args+1)



isOdd :: Int -> Bool
isOdd n = mod n 2 == 1

roundToEven :: Int -> Int
roundToEven n
 | isOdd n    = n+1
 | otherwise  = n



addSize env es =
 [ IMov (Reg EBX) (Const es)
 , IShl (Reg EBX) (Const 1)    -- multiply es by 2 because thats the size
 , IMov (pairAddr 0) (Reg EBX) -- set the value of the element
 ]

addPad env loc =
    [ IMov (Reg EBX) (Const 0) ]
 ++ [ IMov (pairAddr loc) (Reg EBX) ]
 -- [ IAdd (pairAddr loc) (Const 8)]
 -- ++ [ IAnd (pairAddr loc) (HexConst 0xFFFFFFF8)]





tupleCopy env [] _ = []

tupleCopy env (e:es) i =
             [ IMov (Reg EBX) (immArg env e)]           -- store the immediate value of the current element of the tuple

             ++[IMov (pairAddr i) (Reg EBX) -- set the value of the element
             ]
             ++ (tupleCopy env es (i+1))

pairAddr offset = Sized DWordPtr (RegOffset (4 * offset) EAX)

setTag r ty = [ IAdd r (typeTag ty) ]



assertLB env ve vi
 =  [ IMov (Reg ECX) (immArg env vi) ]
 ++ [ ISar (Reg ECX) (Const 1)]
 ++ [ ICmp (Reg ECX) (Const 0)]
 ++ [ IJl (DynamicErr (IndexLow))]

assertUB env ve vi
 =
      [ IMov (Reg EBX) (immArg env ve) ]  -- get the address ve
   ++ [ ISub (Reg EBX) (typeTag TTuple) ] -- remove the tag
   ++ [ IMov (Reg EAX) (Sized DWordPtr (RegOffset 0 EBX))] -- retrieve the size
   ++ [ IMov (Reg ECX) (immArg env vi) ]
   ++ [ ICmp (Reg ECX) (Reg EAX)]
   ++ [ IJg (DynamicErr (IndexHigh))]
assertBound env ve vi
 =
 -- Lower Bound Check
       assertLB env ve vi
    ++ assertUB env ve vi


compileImm :: Env -> IExp -> Instruction
compileImm env v = IMov (Reg EAX) (immArg env v)

compileBinds :: Env -> [Instruction] -> [(ABind, AExp)] -> (Env, [Instruction])
compileBinds env is []     = (env, is)
compileBinds env is (b:bs) = compileBinds env' (is ++ is') bs
  where
    (env', is')            = compileBind env b

compileBind :: Env -> (ABind, AExp) -> (Env, [Instruction])
compileBind env (x, e) = (env', is)
  where
    is                 = compileEnv env e
                      ++ [IMov (stackVar i) (Reg EAX)]
    (i, env')          = pushEnv x env

compilePrim1 :: Tag -> Env -> Prim1 -> IExp -> [Instruction]
compilePrim1 l env Add1   v = compilePrim2 l env Plus  v (Number 1 l)
compilePrim1 l env Sub1   v = compilePrim2 l env Minus v (Number 1 l)
compilePrim1 _ env Print  v = call (builtin "print") [param env v]

compilePrim2 :: Tag -> Env -> Prim2 -> IExp -> IExp -> [Instruction]
compilePrim2 _ env Plus    = arith     env addOp
compilePrim2 _ env Minus   = arith     env subOp
compilePrim2 _ env Times   = arith     env mulOp
compilePrim2 l env Less    = compare l env IJl
compilePrim2 l env Greater = compare l env IJg
compilePrim2 l env Equal   = compare l env IJe

immArg :: Env -> IExp -> Arg
immArg _   (Number n _)  = repr n
immArg _   (Boolean b _) = repr b
immArg env e@(Id x _)    = stackVar (fromMaybe err (lookupEnv x env))
  where
    err                  = abort (errUnboundVar (sourceSpan e) x)
immArg _   e             = panic msg (sourceSpan e)
  where
    msg                  = "Unexpected non-immExpr in immArg: " ++ show (strip e)

strip = fmap (const ())

--------------------------------------------------------------------------------
-- | Arithmetic
--------------------------------------------------------------------------------
arith :: Env -> AOp -> IExp -> IExp  -> [Instruction]
--------------------------------------------------------------------------------
arith env aop v1 v2
  =  IMov (Reg EAX) (immArg env v1)
   : IMov (Reg EBX) (immArg env v2)
   : aop (Reg EAX) (Reg EBX)

addOp :: AOp
addOp a1 a2 = [ IAdd a1 a2
              , overflow
              ]

subOp :: AOp
subOp a1 a2 = [ ISub a1 a2
              , overflow
              ]

mulOp :: AOp
mulOp a1 a2 = [ ISar a1 (Const 1)
              , IMul a1 a2
              , overflow
              ]

overflow :: Instruction
overflow = IJo (DynamicErr ArithOverflow)

--------------------------------------------------------------------------------
-- | Comparisons
--------------------------------------------------------------------------------
-- | @compare v1 v2@ generates the instructions at the
--   end of which EAX is TRUE/FALSE depending on the comparison
--------------------------------------------------------------------------------
compare :: Tag -> Env -> COp -> IExp -> IExp -> [Instruction]
compare l env j v1 v2
   = IMov (Reg EAX) (immArg env v1)
   : IMov (Reg EBX) (immArg env v2)
   : ICmp (Reg EAX) (Reg EBX)
   : boolBranch l j

--------------------------------------------------------------------------------
-- | Assignment
--------------------------------------------------------------------------------
assign :: (Repr a) => Reg -> a -> Instruction
assign r v = IMov (Reg r) (repr v)

--------------------------------------------------------------------------------
-- | Function call
--------------------------------------------------------------------------------
call :: Arg -> [Arg] -> [Instruction]
call f args
  =    ISub (Reg ESP) (Const (4 * k))
  :  [ IPush a | a <- reverse args ]
  ++ [ ICall f
     , IAdd (Reg ESP) (Const (4 * (n + k)))  ]
  where
    n = length args
    k = 4 - (n `mod` 4)

param :: Env -> IExp -> Arg
param env v = Sized DWordPtr (immArg env v)

--------------------------------------------------------------------------------
-- | Branching
--------------------------------------------------------------------------------
branch :: Tag -> COp -> [Instruction] -> [Instruction] -> [Instruction]
branch l j falseIs trueIs = concat
  [ [ j lTrue ]
  , falseIs
  , [ IJmp lDone
    , ILabel lTrue  ]
  , trueIs
  , [ ILabel lDone ]
  ]
  where
    lTrue = BranchTrue i
    lDone = BranchDone i
    i     = snd l

boolBranch :: Tag -> COp -> [Instruction]
boolBranch l j = branch l j [assign EAX False] [assign EAX True]

type AOp = Arg -> Arg -> [Instruction]
type COp = Label -> Instruction

stackVar :: Int -> Arg
stackVar i = RegOffset (-4 * i) EBP

--------------------------------------------------------------------------------
-- | Representing Values
--------------------------------------------------------------------------------

class Repr a where
  repr :: a -> Arg

instance Repr Bool where
  repr True  = HexConst 0xffffffff
  repr False = HexConst 0x7fffffff

instance Repr Int where
  repr n = Const (fromIntegral (shift n 1))

instance Repr Integer where
  repr n = Const (fromIntegral (shift n 1))

instance Repr Field where
  repr Zero = repr (0 :: Int)
  repr One  = repr (1 :: Int)

typeTag :: Ty -> Arg
typeTag TNumber   = HexConst 0x00000000
typeTag TBoolean  = HexConst 0x7fffffff
typeTag TTuple    = HexConst 0x00000001
typeTag TClosure  = HexConst 0x00000005

typeMask :: Ty -> Arg
typeMask TNumber  = HexConst 0x00000001
typeMask TBoolean = HexConst 0x7fffffff
typeMask TTuple   = HexConst 0x00000007
typeMask TClosure = HexConst 0x00000007
