----------------------------------------------------------------------
--- A representation of CHR rules in Curry, an interpreter
--- for CHR rules based on the refined operational semantics of
--- Duck et al. (ICLP 2004), and a compiler into CHR(Prolog).
---
--- To use CHR(Curry), specify the CHR(Curry) rules in a Curry program,
--- load it, add module `CHR` and interpret or compile the rules
--- with `runCHR` or `compileCHR`, respectively. This can be done
--- in one shot with
---
---     > pakcs :l MyRules :add CHR :eval 'compileCHR "MyCHR" [rule1,rule2]' :q
---
--- @author Michael Hanus
--- @version May 2016
--- @category general
----------------------------------------------------------------------

{-# OPTIONS_CYMAKE -Wno-incomplete-patterns -Wno-overlapping #-}

module CHR(CHR,Goal,(/\), (<=>), (==>), (|>), (\\),
           true, false, andCHR, allCHR, chrsToGoal,
           toGoal1, toGoal2, toGoal3, toGoal4, toGoal5, toGoal6,
           (.=.), (./=.), (.<=.), (.>=.), (.>.), (.<.),
           nonvar, ground, anyPrim,
           solveCHR, runCHR, runCHRwithTrace,
           compileCHR, chr2curry
          ) where

import Char
import Findall           (rewriteSome)
import FlatCurry.Types
import FlatCurry.Files
import FlatCurry.Goodies
import FlatCurry.Pretty  (defaultOptions, ppTypeExp)
import List
import Prolog
import Pretty            (pretty)
import SetRBT
import Unsafe -- for tracing
import XML

-------------------------------------------------------------------------------
-- Operator definitions for writing CHRs:

infix 5 .=., ./=., .<=., .>=., .>., .<.
infixr 4 /\
infix 3 <=>
infix 3 ==>
infix 2 \\
infix 1 |>

-------------------------------------------------------------------------------
-- Data types for defining Constraint Handling Rules.

--- The basic data type of Constraint Handling Rules.
data CHR dom chr =
    SimplRule [chr] [PrimConstraint dom] (Goal dom chr)
  | PropaRule [chr] [PrimConstraint dom] (Goal dom chr)
  | SimpaRule [chr] [chr] [PrimConstraint dom] (Goal dom chr)

--- Simplification rule.
(<=>) :: Goal dom chr -> Goal dom chr -> CHR dom chr
g1 <=> g2 =
  if null (primsOfGoal g1)
  then SimplRule (uchrOfGoal g1) [] g2
  else error "Rule with primitive constraint on the left-hand side!"

--- Propagation rule.
(==>) :: Goal dom chr -> Goal dom chr -> CHR dom chr
g1 ==> g2 =
  if null (primsOfGoal g1)
  then PropaRule (uchrOfGoal g1) [] g2
  else error "Rule with primitive constraint on the left-hand side!"

--- Simpagation rule: if rule is applicable, the first constraint is kept
--- and the second constraint is deleted.
(\\) :: Goal dom chr -> CHR dom chr -> CHR dom chr
g1 \\ (SimplRule lchrs guard rcs)
  | not (null (primsOfGoal g1))
   = error "Simpagation rule with primitive kept constraints!"
  | null keptcs -- to omit trivial uses of simpagation rule
   = SimplRule lchrs guard rcs
  | null lchrs -- to omit trivial uses of simpagation rule
   = PropaRule keptcs guard rcs
  | otherwise = SimpaRule keptcs lchrs guard rcs
 where
  keptcs = uchrOfGoal g1

--- A rule with a guard.
(|>) :: CHR dom chr -> Goal dom chr -> CHR dom chr
rule |> g3 = attachGuard rule
 where
  attachGuard (SimplRule lcs guard rcs) =
    if null (uchrOfGoal rcs)
    then SimplRule lcs (guard ++ primsOfGoal rcs) g3
    else error "Rule contains a guard with non-primitive constraints!"
  attachGuard (PropaRule lcs guard rcs) =
    if null (uchrOfGoal rcs)
    then PropaRule lcs (guard ++ primsOfGoal rcs) g3
    else error "Rule contains a guard with non-primitive constraints!"
  attachGuard (SimpaRule h1 h2 guard rcs) =
    if null (uchrOfGoal rcs)
    then SimpaRule h1 h2 (guard ++ primsOfGoal rcs) g3
    else error "Rule contains a guard with non-primitive constraints!"


------------------------------------------------------------------------------
-- Data types for defining CHR goals and constraints.

--- A CHR constraint is either a primitive or a user-defined constraint.
data CHRconstr dom chr = PrimCHR (PrimConstraint dom) | UserCHR chr

--- A CHR goal is a list of CHR constraints (primitive or user-defined).
data Goal dom chr = Goal [CHRconstr dom chr]

--- Conjunction of CHR goals.
(/\) :: Goal dom chr -> Goal dom chr -> Goal dom chr 
(/\) (Goal c1) (Goal c2) = Goal (c1 ++ c2)

--- The always satisfiable CHR constraint.
true :: Goal dom chr 
true = Goal []

--- The always unsatisfiable constraint.
false :: Goal dom chr 
false = primToGoal Fail

--- Join a list of CHR goals into a single CHR goal (by conjunction).
andCHR :: [Goal dom chr] -> Goal dom chr
andCHR = foldr (/\) true

--- Is a given constraint abstraction satisfied by all elements in a list?
allCHR :: (a -> Goal dom chr) -> [a] -> Goal dom chr
allCHR fc = andCHR . map fc

-- Extracts the list of user-defined constraints contained in a CHR goal.
uchrOfGoal :: Goal dom chr -> [chr]
uchrOfGoal (Goal cs) = concatMap uchr cs
 where uchr (PrimCHR _) = []
       uchr (UserCHR c) = [c]

-- Extracts the list of primitive constraints contained in a CHR goal.
primsOfGoal :: Goal dom chr -> [PrimConstraint dom]
primsOfGoal (Goal cs) = concatMap prim cs
 where prim (PrimCHR c) = [c]
       prim (UserCHR _) = []

--- Transforms a list of CHR constraints into a CHR goal.
chrsToGoal :: [chr] -> Goal dom chr
chrsToGoal cs = Goal (map UserCHR cs)

--- Transform unary CHR constraint into a CHR goal.
toGoal1 :: (a -> chr) -> a -> Goal dom chr
toGoal1 c x = Goal [UserCHR (c x)]

--- Transforms binary CHR constraint into a CHR goal.
toGoal2 :: (a -> b -> chr) -> a -> b -> Goal dom chr
toGoal2 c x y = Goal [UserCHR (c x y)]

--- Transforms a ternary CHR constraint into a CHR goal.
toGoal3 :: (a -> b -> c -> chr) -> a -> b -> c -> Goal dom chr
toGoal3 c x y z = Goal [UserCHR (c x y z)]

--- Transforms a CHR constraint of arity 4 into a CHR goal.
toGoal4 :: (a -> b -> c -> d -> chr)
        -> a -> b -> c -> d -> Goal dom chr
toGoal4 con a b c d = Goal [UserCHR (con a b c d)]

--- Transforms a CHR constraint of arity 5 into a CHR goal.
toGoal5 :: (a -> b -> c -> d -> e -> chr)
        -> a -> b -> c -> d -> e -> Goal dom chr
toGoal5 con a b c d e = Goal [UserCHR (con a b c d e)]

--- Transforms a CHR constraint of arity 6 into a CHR goal.
toGoal6 :: (a -> b -> c -> d -> e -> f -> chr)
        -> a -> b -> c -> d -> e -> f -> Goal dom chr
toGoal6 con a b c d e f = Goal [UserCHR (con a b c d e f)]

-----------------------------------------------------------------------------
-- Primitive constraints:
data PrimConstraint a = Eq a a -- equality
                      | Neq a a -- disequality
                      | Fail   -- always unsatisfiable
                      | Compare (a -> a -> Bool) a a -- ordering constraint
                      | Ground a -- ground value
                      | Nonvar a -- not an unbound variable
                      | AnyPrim (() -> Bool) -- user-defined primitive

--- Transforms a primitive constraint into a CHR goal.
primToGoal :: PrimConstraint dom -> Goal dom chr
primToGoal pc = Goal [PrimCHR pc]

--- Primitive syntactic equality on arbitrary terms.
(.=.) :: dom -> dom -> Goal dom chr
x .=. y = primToGoal (Eq x y)

--- Primitive syntactic disequality on ground(!) terms.
(./=.) :: dom -> dom -> Goal dom chr
x ./=. y = primToGoal (Neq x y)

--- Primitive less-or-equal constraint.
(.<=.) :: Ord dom => dom -> dom -> Goal dom chr
x .<=. y = primToGoal (Compare (<=) x y)

--- Primitive greater-or-equal constraint.
(.>=.) :: Ord dom => dom -> dom -> Goal dom chr
x .>=. y = primToGoal (Compare (>=) x y)

--- Primitive less-than constraint.
(.<.) :: Ord dom => dom -> dom -> Goal dom chr
x .<. y = primToGoal (Compare (<) x y)

--- Primitive greater-than constraint.
(.>.) :: Ord dom => dom -> dom -> Goal dom chr
x .>. y = primToGoal (Compare (>) x y)

--- Primitive groundness constraint (useful for guards).
ground :: dom -> Goal dom chr
ground x = primToGoal (Ground x)

--- Primitive nonvar constraint (useful for guards).
nonvar :: dom -> Goal dom chr
nonvar x = primToGoal (Nonvar x)

--- Embed user-defined primitive constraint.
anyPrim :: (() -> Bool) -> Goal dom chr
anyPrim cf = primToGoal (AnyPrim cf)

-- Evaluate primitive constraints.
evalPrimCHR :: Eq a => PrimConstraint a -> Bool
evalPrimCHR (Eq x y)          = x=:=y
evalPrimCHR (Neq x y)         = (x==y) =:= False
evalPrimCHR Fail              = failed
evalPrimCHR (Compare cmp x y) = (cmp x y) =:= True
evalPrimCHR (Nonvar x)        = Unsafe.isVar x =:= False
evalPrimCHR (Ground x)        = Unsafe.isGround x =:= True
evalPrimCHR (AnyPrim cf)      = cf ()


------------------------------------------------------------------------------
-- Interpreter for CHR constraints
------------------------------------------------------------------------------

--- Interpret CHR rules (parameterized over domain variables)
--- for a given CHR goal (second argument) and embed this as
--- a constraint solver in Curry. If user-defined CHR constraints remain
--- after applying all CHR rules, a warning showing the residual
--- constraints is issued.
solveCHR :: (Eq dom, Show chr) => [[dom] -> CHR dom chr] -> Goal dom chr -> Bool
solveCHR prules goal =
  let residual = runCHR prules goal
   in if null residual
      then True
      else trace ("WARNING: residual CHR constraints: "++show residual++"\n")
                 True

------------------------------------------------------------------------
-- The structure and operations for the history of the interpreter.

-- type History = [([Int],Int)] -- entry: constraint indices and rule index
-- emptyHistory  = []
-- extendHistory = (:)
-- inHistory     = elem
type History = SetRBT ([Int],Int) -- entry: constraint indices and rule index

emptyHistory :: Ord a => SetRBT a
emptyHistory  = emptySetRBT (<=)

extendHistory :: a -> SetRBT a -> SetRBT a
extendHistory = insertRBT

inHistory :: a -> SetRBT a -> Bool
inHistory     = elemRBT

------------------------------------------------------------------------
--- Interpret CHR rules (parameterized over domain variables)
--- for a given CHR goal (second argument) and return the remaining
--- CHR constraints.
runCHR :: Eq dom => [[dom] -> CHR dom chr] -> Goal dom chr -> [chr]
runCHR prules goal = evalCHR False prules goal

--- Interpret CHR rules (parameterized over domain variables)
--- for a given CHR goal (second argument) and return the remaining
--- CHR constraints. Trace also the active and passive constraints
--- as well as the applied rule number during computation.
runCHRwithTrace :: Eq dom => [[dom] -> CHR dom chr] -> Goal dom chr -> [chr]
runCHRwithTrace prules goal = evalCHR True prules goal

-- Interpreter for CHR (refined semantics):
evalCHR :: Eq dom => Bool -> [[dom] -> CHR dom chr] -> Goal dom chr -> [chr]
evalCHR withtrace urules (Goal goal)
   | evalConstr gidx emptyHistory chrgoal [] result
   = map snd result
 where
  tracing s = if withtrace then trace s else id

  result free

  rules = zip [1..] urules

  (gidx,chrgoal) = numberCHR 0 goal

  solvePrims = all evalPrimCHR

  -- evaluate list of active constraints:
  evalConstr gi hist gl cstore finalcs = tracing (showAnyTerm (gl,cstore)) $
                                         evalC gl cstore finalcs
   where
    evalC [] cs rcs = cs =:= rcs -- no active constraints left to work on
    evalC (PrimCHR pc : gs) cs rcs = -- awake all passive constraints:
      tracing ("Evaluate primitive: " ++ showAnyTerm pc) $
      evalPrimCHR pc & evalConstr gi hist (map UserCHR cs ++ gs) [] rcs
    evalC (UserCHR c  : gs) cs rcs =
      (normalForm c) -- necessary to evaluate functions in c's arguments
         `seq` tryRules gi hist rules c gs cs rcs

  -- try to apply CHR rules in sequential order to first active constraint:
  tryRules gi hs [] c gs cs rcs = -- no CHR rule applicable, try solve a prim:
    maybe (tracing "Suspend constraint" $
           evalConstr gi hs gs (c:cs) rcs) -- suspend first active constraint
          (\ (pc,mgs) -> tracing ("Evaluate primitive: " ++ showAnyTerm pc) $
                         evalPrimCHR pc & -- awake all passive constraints:
                         evalConstr gi hs (map UserCHR (c:cs) ++ mgs) [] rcs)
          (extractPrim gs)
  tryRules gi hist ((ri,r) : rs) c gs cs rcs =
    maybe (tryRules gi hist rs c gs cs rcs)
          (\ (newcs,newgs,remcs,is) ->
             if (is,ri) `inHistory` hist -- rule already applied?
             then tryRules gi hist rs c gs cs rcs
             else --trace (show (is,ri)) $
                  let (gj,inewcs) = numberCHR gi newcs
                   in tracing ("Apply rule " ++ show ri) $
                      evalConstr gj
                                 (if null is then hist
                                  else extendHistory (is,ri) hist)
                                 (inewcs++newgs)
                                 remcs rcs)
          (rewriteSome (applyRule (r unknown) c gs cs))

  -- Apply a CHR rule to an active constraint and constraint store
  -- and return the new goal, remaining constraint store and indices
  -- of the CHR constraints matched for the left-hand side, if it is
  -- a propogation rule (in this case, it is stored in the history to
  -- avoid re-application of the same rule).
  applyRule (SimplRule lchrs guard (Goal rchrs)) (_,c) gs cs
    | deleteSome c lchrs =:= lhs & findDelete lhs cs =:= (delcs,remcs)
      &> solvePrims guard
    = (rchrs,gs,remcs,[])                         where lhs,delcs,remcs free
  applyRule (PropaRule lchrs guard (Goal rchrs)) (i,c) gs cs
    | deleteSome c lchrs =:= lhs & findDelete lhs cs =:= (delcs,_)
      &> solvePrims guard
    = (rchrs, UserCHR (i,c) : gs, cs, i : map fst delcs)  where lhs,delcs free
  applyRule (SimpaRule kept lchrs guard (Goal rchrs)) (_,c) gs cs
    | deleteSome c lchrs =:= lhs & findDelete (kept++lhs) cs =:= (delcs,remcs)
      &> solvePrims guard
    = (rchrs, gs, take (length kept) delcs ++ remcs, [])
   where lhs,delcs,remcs free
  applyRule (SimpaRule kept lchrs guard (Goal rchrs)) (i,c) gs cs
    | deleteSome c kept =:= kc & findDelete (kc++lchrs) cs =:= (delcs,remcs)
      &> solvePrims guard
    = (rchrs, UserCHR (i,c) : gs, take (length kc) delcs ++ remcs, [])
   where kc,delcs,remcs free

-- Auxiliary operations:

-- Find a list of elements in another list and return the remaining ones:
findDelete :: [a] -> [(Int,a)] -> ([(Int,a)],[(Int,a)])
findDelete []     cs = ([],cs)
findDelete (x:xs) cs = let (z,ds) = del x cs
                           (zs,es) = findDelete xs ds
                        in (z:zs,es)
 where
  del e (z:zs) | e=:=snd z = (z,zs)
  del e (z:zs) = let (y,ys) = del e zs in (y, z:ys)

deleteSome :: a -> [a] -> [a]
deleteSome e (z:zs) | e=:=z = zs
deleteSome e (z:zs) = z : deleteSome e zs

-- Finds and deletes the first primitive constraint in a CHR goal:
extractPrim :: [CHRconstr dom chr]
            -> Maybe (PrimConstraint dom, [CHRconstr dom chr])
extractPrim [] = Nothing
extractPrim (PrimCHR pc : cs) = Just (pc, cs)
extractPrim (UserCHR c : cs) =
  maybe Nothing
        (\ (pc,rcs) -> Just (pc, UserCHR c : rcs))
        (extractPrim cs)

-- Add a unique number to each CHR constraint.
numberCHR :: Int -> [CHRconstr dom chr] -> (Int, [CHRconstr dom (Int,chr)])
numberCHR i [] = (i,[])
numberCHR i (PrimCHR pc : cs) =
  let (j,ics) = numberCHR i cs in (j, PrimCHR pc : ics)
numberCHR i (UserCHR c : cs) =
  let (j,ics) = numberCHR (i+1) cs in (j, UserCHR (i,c) : ics)


----------------------------------------------------------------------
-- Compiler from Curry CHR rules into CHR(Prolog) rules where
-- operations from the Curry program can also be called from the
-- CHR(Prolog) code.

--- Compile a list of CHR(Curry) rules into CHR(Prolog) and store its interface
--- in a Curry program (name given as first argument).
compileCHR :: String -> [[dom] -> CHR dom chr] -> IO ()
compileCHR currymod rules
  | null rids = putStrLn "No CHR rules to compile."
  | any (/=sourcemodname) (map fst rids)
    = error "Cannot compile CHR rules from different modules!"
  | otherwise = compileRules sourcemodname currymod (map snd rids)
 where
  rids = map ruleId rules
  sourcemodname = fst (head rids)

-- extract the qualified name of a rule:
ruleId :: ([dom] -> CHR dom chr) -> QName
ruleId rule =
  let rcallstring = showAnyQExpression rule -- "(partcall 1 qid [])"
      qid = takeWhile (not . isSpace) (drop (length "(partcall 1 ") rcallstring)
      (mname,rname) = break (=='.') qid
   in (mname, tail rname)

-- compile all specifed CHR rules to CHR(Prolog):
compileRules :: String -> String -> [String] -> IO ()
compileRules modname chrmodname rids = do
  (Prog _ _ _ fdecls opdecls) <- readFlatCurry modname
  let pmodname = chrmodname++"_prim"
      getftype = getFuncType fdecls
      rdefs = filter (\ (Func fname _ _ _ _) -> snd fname `elem` rids) fdecls
      (chrs,_) = unzip (map (compileRule getftype []) (map funcRule rdefs))
      allchrs = nub (concat chrs)
      (_,trules) = unzip (map (compileRule getftype allchrs)
                         (map funcRule rdefs))
      allchrtypes = zip allchrs (map getftype (map fst allchrs))
      curryprog = showCHRModule modname chrmodname opdecls allchrtypes
      prologprog = unlines $
        map showPlClause
          ([PlDirective
             [PlLit "module"
               [PlAtom pmodname,
                plList (map (\ (qcname,carity)->
                         PlStruct "/" [PlAtom (showCName ("prim_"++snd qcname)),
                                       PlInt (carity+1)])
                            allchrs)]],
            PlDirective [PlLit "use_module"
                               [PlStruct "library" [PlAtom "chr"]]]] ++
           map (\ (p,a) ->
                  PlDirective
                     [PlLit "chr_constraint"
                            [PlStruct "/" [PlAtom (showPlName p), PlInt a]]])
               allchrs) ++
        ["","% CHR rules:"] ++ trules ++ ["","% Curry/Prolog interface:"] ++
        map (showPlClause . chrPrologPrimDefinition) allchrs ++
        ["","% Auxiliary predicates:",
         "sunif(X,Y) :- user:evalToken(E), user:hnf('Prelude.=:='(X,Y),_,E,_).",
         "eval(X) :- user:evalToken(E), user:hnf(X,_,E,_)."]
  writeFile (chrmodname++".curry") curryprog
  writeXmlFileWithParams (chrmodname++".prim_c2p")
          [DtdUrl "http://www.informatik.uni-kiel.de/~pakcs/primitives.dtd"]
          (constraints2xml pmodname allchrs)
  writeFile (pmodname++".pl") prologprog
  --putStrLn curryprog
  --putStrLn prologprog
  putStrLn $ "Curry interface to CHR(Prolog) written to "++chrmodname++".curry"

getFuncType :: [FuncDecl] -> (String,String) -> TypeExpr
getFuncType fdecls qfname =
  maybe (error $ showQName qfname ++ " not found!")
        funcType
        (find (\ (Func qf _ _ _ _) -> qf == qfname) fdecls)
  
chrPrologPrimDefinition :: (QName,Int) -> PlClause
chrPrologPrimDefinition (qcname,carity) =
  PlClause
    (showCName ("prim_"++snd qcname))
    (map PlVar (map (\i->"X"++show i) [1..carity] ++ ["R"]))
    [PlLit (showPlName qcname) (map (\i->PlVar ("X"++show i)) [1..carity]),
     PlLit "=" [PlVar "R", PlAtom "Prelude.True"]]


-- show Curry module as interface to CHR solver implemented in Prolog:
showCHRModule :: String -> String -> [OpDecl] ->
                 [((QName,Int),TypeExpr)] -> String
showCHRModule orgmod chrmod opdecls constraints = unlines $
  ["module "++chrmod++exports++" where","",
  -- import original modules so that their code is available for
  -- evaluating primitive (Curry-defined) constraints
   "import qualified CHR(chr2curry)",
   "import CHRcompiled",
   "import qualified "++orgmod,""] ++
  map showOpDecl chropdecls ++ [""] ++
  map showCurryConstraint constraints
 where
  exports = "(module CHRcompiled" ++
            concatMap (',':) (map (showCName . snd) chrqnames) ++ ")"
  chrqnames = map (fst . fst) constraints
  chropdecls = filter (\ (Op qop _ _) -> qop `elem` chrqnames) opdecls

-- show operator declaration
showOpDecl :: OpDecl -> String
showOpDecl (Op op fixity prec) = unwords [showFixity fixity,show prec,showOp op]
 where
  showFixity InfixOp  = "infix"
  showFixity InfixlOp = "infixl"
  showFixity InfixrOp = "infixr"

  showOp (_,on) = if isAlpha (head on) then '`':on++"`" else on

showCurryConstraint :: ((QName,Int),TypeExpr) -> String
showCurryConstraint (((_,cname),carity),ctype) =
  let cargtypes = argTypes carity ctype in
  showCName cname ++" :: "++ concatMap (++" -> ") cargtypes
    ++"Goal "++ showCurryType (resultType carity ctype) ++"\n"++
  showCName cname ++ concatMap (\i->" x"++show i) [1..carity] ++ " = Goal " ++
    take carity (repeat '(') ++
    showCName ("prim_"++cname) ++
    concatMap (\i->" $!! x"++show i++")") [1..carity] ++ "\n\n" ++
  showCName ("prim_"++cname) ++ " :: " ++
            concatMap (++" -> ") cargtypes ++ "Bool\n" ++
  showCName ("prim_"++cname) ++ " external\n"
 where
   resultType arity tp =
     if arity==0 then let TCons _ [_,chrtype] = tp
                       in chrtype
                 else let FuncType _ rtype = tp
                       in resultType (arity-1) rtype

   argTypes arity ftype = if arity==0 then [] else
     let FuncType atype rtype = ftype
      in showCurryType atype : argTypes (arity-1) rtype

-- generate prim_c2p specification of external operations:
constraints2xml :: String -> [(QName,Int)] -> XmlExp
constraints2xml prologmod constraints =
  xml "primitives" (map constraint2xml constraints)
 where
   constraint2xml ((_,cname),carity) =
     XElem "primitive" [("name",showCName ("prim_"++cname)),
                        ("arity",show carity)]
           [xml "library" [xtxt prologmod],
            xml "entry" [xtxt (showCName ("prim_"++cname))]]

-- compile a single CHR rule:
compileRule :: (QName -> TypeExpr) -> [(QName,Int)] -> Rule
            -> ([(QName,Int)],String)
compileRule getftype chrs (Rule _ rhs) =
  let (_,rchrs,trule) = exp2CHR 100 (firstBranch rhs)
   in (rchrs, trule ++ ".")
 where
  exp2CHR i exp@(Comb FuncCall qf [a1,a2])
    | qf == (chrMod,"<=>")  = let (j, chrs1,tgoal1) = transGoal i a1
                                  (k,_,tgoal2) = transGoal j a2
                               in (k, chrs1, sg tgoal1 ++" <=> "++ sg tgoal2)
    | qf == (chrMod,"==>")  = let (j,chrs1,tgoal1) = transGoal i a1
                                  (k,_,tgoal2) = transGoal j a2
                               in (k, chrs1, sg tgoal1 ++" ==> "++ sg tgoal2)
    | qf == (chrMod,"\\\\") = let (j,chrs1,tgoal1) = transGoal i a1
                                  (k,chrs2,trule2) = exp2CHR j a2
                               in (k, chrs1++chrs2, sg tgoal1 ++" \\ "++ trule2)
    | qf == (chrMod,"|>")   = let (j,chrs1,trule1) = exp2CHR i a1
                                  (k,_,tgoal2) = transGoal j a2
                               in (k, chrs1, trule1 ++" | "++ sg tgoal2)
    | otherwise = error ("Cannot translate CHR rule: " ++ show exp)
   where sg = showPlGoals

  transGoal i exp = case reduceApply exp of
    Comb FuncCall qf args -> if fst qf == chrMod then transCHRPred i qf args
                                                 else transUserPred i qf args
    _ -> error ("Cannot translate CHR literal: " ++ show exp)

  transCHRPred i (_,cname) args
   | cname=="/\\" =
      let (j,chrs1,tgoal1) = transGoal i (args!!0)
          (k,chrs2,tgoal2) = transGoal j (args!!1)
       in (k, chrs1++chrs2, tgoal1 ++ tgoal2)
   | cname=="nonvar" = (i, [], [PlLit "nonvar" [transArg (args!!0)]])
   | cname=="ground" = (i, [], [PlLit "ground" [transArg (args!!0)]])
   | cname=="true"   = (i, [], [PlLit "true" []])
   | cname=="false"  = (i, [], [PlLit "fail" []])
   | otherwise = maybe (error $ "Illegal CHR constraint: CHR."++cname)
                       (\chr2pl -> (i, [], [chr2pl (map transArg args)]))
                       (lookup cname chrPrims)

  transUserPred i qf args =
    let (j,plits,plit) = flattenLiteral i qf args
        fplit = if qf `elem` map fst chrs
                then plit
                else if isCHRType (getftype qf)
                     then let PlLit pn pargs = plit
                           in PlLit "eval" [PlStruct "CHR.chr2curry"
                                                     [PlStruct pn pargs]]
                     else error ("Operation '"++snd qf++
                                 "' is not a CHR constraint!")
     in (j, [(qf,length args)], plits ++ [fplit])

-- check whether the type is a type of a CHR constraint
isCHRType :: TypeExpr -> Bool
isCHRType texp = case texp of
  FuncType _ rt -> isCHRType rt
  TCons qtc _   -> qtc == (chrMod,"Goal")
  _             -> False

-- get the first branch of a function definition
firstBranch :: Expr -> Expr
firstBranch exp = case exp of
  Case _ _ (Branch _ bexp : brs) ->
      if null brs
      then firstBranch bexp
      else error ("CHR rule with more than one branch: "++show exp)
  Free _ fexp                   -> firstBranch fexp
  _                             -> exp

-- reduce h.o. applications to a known function:
reduceApply :: Expr -> Expr
reduceApply exp = case exp of
  Comb FuncCall ("Prelude","apply") [a1,a2] ->
    let ra1 = reduceApply a1 in
    case ra1 of
      Comb FuncCall qf fargs -> Comb FuncCall qf (fargs++[a2])
      _ -> Comb FuncCall ("Prelude","apply") [ra1,a2]
  _ -> exp

-- Translation table for primitive CHR constraints:
chrPrims :: [(String,[PlTerm] -> PlGoal)]
chrPrims =
 [(".=.", \args -> PlLit "sunif" args),
  ("./=.",\args -> PlLit "sunif" [relApply "Prelude.==" args, pfalse]),
  (".>=.",\args -> PlLit "sunif" [relApply "Prelude.>=" args, ptrue]),
  (".<=.",\args -> PlLit "sunif" [relApply "Prelude.<=" args, ptrue]),
  (".>.", \args -> PlLit "sunif" [relApply "Prelude.>"  args, ptrue]),
  (".<.", \args -> PlLit "sunif" [relApply "Prelude.<"  args, ptrue])]
 where
  ptrue  = PlAtom "Prelude.True"
  pfalse = PlAtom "Prelude.False"
  relApply rel args = foldl (\f x -> PlStruct "Prelude.apply" [f,x])
                            (PlStruct rel [head args])
                            (tail args)

-- Translate an argument of a CHR constraint:
transArg :: Expr -> PlTerm
transArg e = case e of
  Lit (Intc i)          -> PlInt i
  Lit (Floatc f)        -> PlFloat f
  Var i                 -> PlVar ('X' : show i)
  Comb FuncCall qf args -> PlStruct (showPlName qf) (map transArg args)
  Comb ConsCall qf args -> PlStruct (showPlName qf) (map transArg args)
  _                     -> error ("Not yet translatable argument: "++show e)

-- Flatten a CHR literal: if arguments contain function calls,
-- add unification constraints for these arguments.
flattenLiteral :: Int -> QName -> [Expr] -> (Int,[PlGoal],PlGoal)
flattenLiteral i qf args =
  let (j,flits,fargs) = flattenArgs i args
   in (j, flits, PlLit (showPlName qf) (map transArg fargs))

-- Replace non-variable arguments by equalities for new variables.
-- The first argument and result is a counter for indexing new variables.
-- The second result is the Prolog code for new equalities.
flattenArgs :: Int -> [Expr] -> (Int,[PlGoal],[Expr])
flattenArgs i [] = (i,[],[])
flattenArgs i (arg:args) =
  if funcArg arg
  then let (j,flits,fargs) = flattenArgs (i+1) args
        in (j, PlLit "sunif" [PlVar ("X"++show i), transArg arg] : flits,
               Var i:fargs)
  else let (j,flits,fargs) = flattenArgs i args
        in (j, flits, arg : fargs)
 where
  funcArg e = case e of
    Lit _ -> False
    Var _ -> False
    Comb ConsCall _ cargs -> any funcArg cargs
    _     -> True

-- Shows a qualified name:
showQName :: QName -> String
showQName (mname,fname) = mname++"."++fname

-- Shows a name in Curry syntax, i.e., encode special characters as alphanum.
showCName :: String -> String
showCName s
  | all (\c -> isAlphaNum c || c=='_') s = s
  | isAlpha (head s) = concatMap (\c -> if isAlphaNum c || c=='_'
                                        then [c]
                                        else 'X':show (ord c))
                                 s
  | otherwise = "("++s++")"

-- Shows a qualified name in PAKCS Prolog syntax, i.e.,
-- encode special characters.
showPlName :: QName -> String
showPlName qn@(mn,fn)
  | qn == ("Prelude","[]") = "[]"
  | qn == ("Prelude",":")  = "."
  | all (\c -> isAlphaNum c || c=='_') fn = showQName qn
  | length fn > 1 && head fn == '_' = mn ++ '.' : concatMap encodeChar fn
  | otherwise = showQName qn
 where
  encodeChar c = if isAlphaNum c || c=='_' || c=='.'
                   then [c]
                   else let oc = ord c
                         in [''', intToDigit (oc `div` 16),
                                  intToDigit (oc `mod` 16)]

-- The name of the Curry CHR module:
chrMod :: String
chrMod = "CHR"

----------------------------------------------------------------------
-- Auxiliaries used in the compiled CHR(Prolog) code.

--- Transforms a primitive CHR constraint into a Curry constraint.
--- Used in the generated CHR(Prolog) code to evaluated primitive
--- constraints.
chr2curry :: Eq dom => CHR.Goal dom chr -> Bool
chr2curry (CHR.Goal c) = case c of
  [CHR.PrimCHR pc] -> CHR.evalPrimCHR pc
  _                -> error "CHRcompiled.chr2curry: unexpected argument!"

----------------------------------------------------------------------

-- Use FlatCurry pretty printer to show a non-top-level type expression.
showCurryType :: TypeExpr -> String
showCurryType te = '(' : pretty 78 (ppTypeExp defaultOptions te) ++ ")"

----------------------------------------------------------------------
