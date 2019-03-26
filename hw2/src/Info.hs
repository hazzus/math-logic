module Info where

-- Information data class for Expression
data Information
  = Hypothesis !Int
  | Axiom !Int
  | ModusPonens !(Int, Int)
  | Wrong
  | Duplicate
  deriving (Eq)

instance Show Information where
  show (Axiom a)       = "Ax. sch. " ++ show a
  show (Hypothesis a)  = "Hypothesis " ++ show a
  show (ModusPonens a) = "M.P. " ++ show a
  show (Wrong)         = "Wrong"
  show (Duplicate)     = "Duplicate"
