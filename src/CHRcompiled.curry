----------------------------------------------------------------------
--- This module defines the structure of CHR goals and some constructors
--- to be used in compiled CHR(Curry) rules.
--- Furthermore, it defines an operation `solveCHR` to solve
--- a CHR goal as a constraint.
---
--- This module is imported in compiled CHR(Curry) programs,
--- compare library `CHR`.
---
--- @author Michael Hanus
--- @version February 2015
--- @category general
----------------------------------------------------------------------

module CHRcompiled where

import qualified CHR

infixr 4 /\

--- A typed CHR goal.
--- Since types are not present at run-time in compiled,
--- we use a phantom type to parameterize goals over CHR constraints.
--- The argument of the goal is the constraint implementing the goal
--- with the compiled CHR(Prolog) program.
data Goal _ = Goal Bool

--- Conjunction of CHR goals.
(/\) :: Goal chr -> Goal chr -> Goal chr 
(/\) (Goal g1) (Goal g2) = Goal (g1 & g2)

--- The always satisfiable CHR constraint.
true :: Goal _
true = Goal True

--- The always failing constraint.
fail :: Goal _
fail = Goal failed

--- Join a list of CHR goals into a single CHR goal (by conjunction).
andCHR :: [Goal chr] -> Goal chr
andCHR = foldr (/\) true

--- Is a given constraint abstraction satisfied by all elements in a list?
allCHR :: (a -> Goal chr) -> [a] -> Goal chr
allCHR fc = andCHR . map fc


--- Evaluate a given CHR goal and embed this as a constraint in Curry.
--- Note: due to limitations of the CHR(Prolog) implementation,
--- no warning is issued if residual constraints remain after the evaluation.
solveCHR :: Goal chr -> Bool
solveCHR (Goal g) | g = warnSuspendedConstraints True

--- Primitive operation that issues a warning if there are some
--- suspended constraints in the CHR constraint store.
--- If the argument is true, then all suspended constraints are shown,
--- otherwise only the first one.
warnSuspendedConstraints :: Bool -> Bool
warnSuspendedConstraints external

