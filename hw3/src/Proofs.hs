module Proofs where

import Axioms         (checkAxiom)
import Syntax
import Evaluator      (evaluate)
import Deduction      (deduct)


masks1 = [[0], [1]]

masks2 = [[0, 0], [0, 1], [1, 0], [1, 1]]

masks3 = [[0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1]]


generateHyps :: [Expression] -> [Int] -> [Expression] -> [Expression]
generateHyps enough mask other = enough ++ helperGen mask other where
  helperGen (m : mask) (o : other) =
    if m == 1
      then o : helperGen mask other
      else (Neg o) : helperGen mask other
  helperGen []         []          = []


makeProof :: Expression -> [Expression] -> [Expression] -> [Expression]
makeProof expr enough other =
  (excludeLemmas expr) $ makeFullProofs expr enough other


excludeLemmas :: Expression -> [([Expression], [Expression])] -> [Expression]
excludeLemmas expr [(hyps, x)] = x
excludeLemmas expr ap@(proof1 : (proof2 : proofs)) = (excludeLemmas expr) $ pairlyConcatenate ap where
   pairlyConcatenate :: [([Expression], [Expression])] -> [([Expression],[Expression])]
   pairlyConcatenate (one : (two : other)) = concatProofs one two : pairlyConcatenate other
   pairlyConcatenate []                    = []
   pairlyConcatenate _                     = error "You screwed up!"

   concatProofs :: ([Expression], [Expression]) -> ([Expression], [Expression]) -> ([Expression], [Expression])
   concatProofs f@(hyp1, one) s@(hyp2, two) = (reverse $ tail $ reverse hyp1, newProof) where
     -- last hyp2 is positive (according to masks)
     newProof = deduct f  ++ deduct s ++ excludingThird p ++
       [
         Binary To (Binary To (p) (alpha)) (Binary To (Binary To (Neg (p)) (alpha)) (Binary To (Binary Or (p) (Neg (p))) (alpha))),
         Binary To (Binary To (Neg (p)) (alpha)) (Binary To (Binary Or (p) (Neg (p))) (alpha)),
         Binary To (Binary Or (p) (Neg (p))) (alpha),
         alpha
       ]
     p = last hyp2
     alpha = expr



makeFullProofs :: Expression -> [Expression] -> [Expression] -> [([Expression], [Expression])]
makeFullProofs expr enough other =
  if lenough == 0
    then genProofs [[]] expr enough other
    else if lenough == 1
            then genProofs masks1 expr enough other
            else if lenough == 2
                    then genProofs masks2 expr enough other
                    else genProofs masks3 expr enough other
  where
    lenough = length other -- be carefull


genProofs :: [[Int]] -> Expression -> [Expression] -> [Expression] -> [([Expression], [Expression])]
genProofs (curMask : masks) expr enough other =
  (hyps ,generateProof hyps expr) : (genProofs masks expr enough other)
  where
    hyps = generateHyps enough curMask other
genProofs []                _    _      _     = []


generateProof :: [Expression] -> Expression -> [Expression]
generateProof hyps expr =
  case expr of
    _ | checkAxiom expr /= 0 -> [expr]
    Binary op alpha beta       -> generateOperandProof alpha beta
    Neg (Binary op alpha beta) -> generateOperandProof alpha beta
    Neg (Neg alpha)         -> (generateProof hyps alpha) ++ (proofAToNegNegA alpha)
    _                   -> [expr] -- as hypothesis
  where
    mask = 1 : mask
    generateOperandProof :: Expression -> Expression -> [Expression]
    generateOperandProof alpha beta =
      myalpha_proof ++ mybeta_proof ++ op_proof
      where
        myalpha       = valid_expr alpha
        mybeta        = valid_expr beta
        valid_expr e  = if evaluate mask hyps e then e else (Neg e)
        myalpha_proof = generateProof hyps myalpha
        mybeta_proof  = generateProof hyps mybeta
        op_proof      =
          case expr of
            -- and
            Binary And gamma delta       | gamma       == myalpha && delta       == mybeta -> proofAndAB alpha beta
            Neg (Binary And gamma delta) | (Neg gamma) == myalpha && delta       == mybeta -> proofNegAndNegAB alpha beta
                                 | gamma       == myalpha && (Neg delta) == mybeta -> proofNegAndANegB alpha beta
                                 | (Neg gamma) == myalpha && (Neg delta) == mybeta -> proofNegAndNegANegB alpha beta
            -- or
            Binary Or  gamma delta       | gamma       == myalpha && delta       == mybeta -> proofOrAB alpha beta
                                 | (Neg gamma) == myalpha && delta       == mybeta -> proofOrNegAB alpha beta
                                 | gamma       == myalpha && (Neg delta) == mybeta -> proofOrANegB alpha beta
            Neg (Binary Or  gamma delta) | (Neg gamma) == myalpha && (Neg delta) == mybeta -> proofNegOrNegANegB alpha beta
            -- to
            Binary To  gamma delta       | gamma       == myalpha && delta       == mybeta -> proofToAB alpha beta
                                 | (Neg gamma) == myalpha && delta       == mybeta -> proofToNegAB alpha beta
                                 | (Neg gamma) == myalpha && (Neg delta) == mybeta -> proofToNegANegB alpha beta
            Neg (Binary To  gamma delta) | gamma       == myalpha && (Neg delta) == mybeta -> proofNegToANegB alpha beta


proofAToNegNegA alpha =
  [
    alpha,
    Binary To (Neg (alpha)) (Binary To (Binary To (Neg (alpha)) (Neg (alpha))) (Neg (alpha))),
    Binary To (Neg (alpha)) (Binary To (Neg (alpha)) (Neg (alpha))),
    Binary To (Binary To (Neg (alpha)) (Binary To (Neg (alpha)) (Neg (alpha)))) (Binary To (Binary To (Neg (alpha)) (Binary To (Binary To (Neg (alpha)) (Neg (alpha))) (Neg (alpha)))) (Binary To (Neg (alpha)) (Neg (alpha)))),
    Binary To (Binary To (Neg (alpha)) (Binary To (Binary To (Neg (alpha)) (Neg (alpha))) (Neg (alpha)))) (Binary To (Neg (alpha)) (Neg (alpha))),
    Binary To (Neg (alpha)) (Neg (alpha)),
    Binary To (alpha) (Binary To (Neg (alpha)) (alpha)),
    Binary To (Neg (alpha)) (alpha),
    Binary To (Binary To (Neg (alpha)) (alpha)) (Binary To (Binary To (Neg (alpha)) (Neg (alpha))) (Neg (Neg (alpha)))),
    Binary To (Binary To (Neg (alpha)) (Neg (alpha))) (Neg (Neg (alpha))),
    Neg (Neg (alpha))
  ]

proofAndAB alpha beta          = --[Var ("PROOF " ++ show alpha       ++ ", " ++ show beta       ++ "|-" ++ show (Binary And alpha beta))]
  [
    Binary To (alpha) (Binary To (beta) (Binary And (alpha) (beta))),
    alpha,
    Binary To (beta) (Binary And (alpha) (beta)),
    beta,
    Binary And (alpha) (beta)
  ]

proofNegAndNegAB alpha beta    = --[Var ("PROOF " ++ show (Neg alpha) ++ ", " ++ show beta       ++ "|-" ++ show (Neg (Binary And alpha beta)))]
  [
    Neg (alpha),
    beta,
    Binary To (Binary And (alpha) (beta)) (alpha),
    Binary To (Neg (alpha)) (Binary To (Binary And (alpha) (beta)) (Neg (alpha))),
    Binary To (Binary And (alpha) (beta)) (Neg (alpha)),
    Binary To (Binary To (Binary And (alpha) (beta)) (alpha)) (Binary To (Binary To (Binary And (alpha) (beta)) (Neg (alpha))) (Neg (Binary And (alpha) (beta)))),
    Binary To (Binary To (Binary And (alpha) (beta)) (Neg (alpha))) (Neg (Binary And (alpha) (beta))),
    Neg (Binary And (alpha) (beta))
  ]

proofNegAndANegB alpha beta    = --[Var ("PROOF " ++ show alpha       ++ ", " ++ show (Neg beta) ++ "|-" ++ show (Neg (Binary And alpha beta)))]
  [
    alpha,
    Neg (beta),
    Binary To (Binary And (alpha) (beta)) (beta),
    Binary To (Neg (beta)) (Binary To (Binary And (alpha) (beta)) (Neg (beta))),
    Binary To (Binary And (alpha) (beta)) (Neg (beta)),
    Binary To (Binary To (Binary And (alpha) (beta)) (beta)) (Binary To (Binary To (Binary And (alpha) (beta)) (Neg (beta))) (Neg (Binary And (alpha) (beta)))),
    Binary To (Binary To (Binary And (alpha) (beta)) (Neg (beta))) (Neg (Binary And (alpha) (beta))),
    Neg (Binary And (alpha) (beta))
  ]

proofNegAndNegANegB alpha beta = --[Var ("PROOF " ++ show (Neg alpha) ++ ", " ++ show (Neg beta) ++ "|-" ++ show (Neg (Binary And alpha beta)))]
  [
    Neg (alpha),
    Neg (beta),
    Binary To (Binary And (alpha) (beta)) (alpha),
    Binary To (Neg (alpha)) (Binary To (Binary And (alpha) (beta)) (Neg (alpha))),
    Binary To (Binary And (alpha) (beta)) (Neg (alpha)),
    Binary To (Binary To (Binary And (alpha) (beta)) (alpha)) (Binary To (Binary To (Binary And (alpha) (beta)) (Neg (alpha))) (Neg (Binary And (alpha) (beta)))),
    Binary To (Binary To (Binary And (alpha) (beta)) (Neg (alpha))) (Neg (Binary And (alpha) (beta))),
    Neg (Binary And (alpha) (beta))
  ]

proofOrAB alpha beta           = --[Var ("PROOF " ++ show alpha       ++ ", " ++ show beta       ++ "|-" ++ show (Binary Or alpha beta))]
  [
    Binary To (alpha) (Binary Or (alpha) (beta)),
    alpha,
    Binary Or (alpha) (beta)
  ]


proofOrNegAB alpha beta        = --[Var ("PROOF " ++ show (Neg alpha) ++ ", " ++ show beta       ++ "|-" ++ show (Binary Or alpha beta))]
  [
    Binary To (beta) (Binary Or (alpha) (beta)),
    beta,
    Binary Or (alpha) (beta)
  ]

proofOrANegB alpha beta        = --[Var ("PROOF " ++ show alpha       ++ ", " ++ show (Neg beta) ++ "|-" ++ show (Binary Or alpha beta))]
  proofOrAB alpha beta

proofNegOrNegANegB alpha beta  = --[Var ("PROOF " ++ show (Neg alpha) ++ ", " ++ show (Neg beta) ++ "|-" ++ show (Neg (Binary Or alpha beta)))]
  [
    Neg (alpha),
    Neg (beta),
    Binary To (Binary To (Neg (alpha)) (Binary To (Neg (beta)) (Neg (alpha)))) (Binary To (alpha) (Binary To (Neg (alpha)) (Binary To (Neg (beta)) (Neg (alpha))))),
    Binary To (Neg (alpha)) (Binary To (Neg (beta)) (Neg (alpha))),
    Binary To (alpha) (Binary To (Neg (alpha)) (Binary To (Neg (beta)) (Neg (alpha)))),
    Binary To (Neg (alpha)) (Binary To (alpha) (Neg (alpha))),
    Neg (alpha),
    Binary To (alpha) (Neg (alpha)),
    Binary To (Binary To (alpha) (Neg (alpha))) (Binary To (Binary To (alpha) (Binary To (Neg (alpha)) (Binary To (Neg (beta)) (Neg (alpha))))) (Binary To (alpha) (Binary To (Neg (beta)) (Neg (alpha))))),
    Binary To (Binary To (alpha) (Binary To (Neg (alpha)) (Binary To (Neg (beta)) (Neg (alpha))))) (Binary To (alpha) (Binary To (Neg (beta)) (Neg (alpha)))),
    Binary To (alpha) (Binary To (Neg (beta)) (Neg (alpha))),
    Binary To (Binary To (alpha) (Binary To (Neg (beta)) (alpha))) (Binary To (alpha) (Binary To (alpha) (Binary To (Neg (beta)) (alpha)))),
    Binary To (alpha) (Binary To (Neg (beta)) (alpha)),
    Binary To (alpha) (Binary To (alpha) (Binary To (Neg (beta)) (alpha))),
    Binary To (alpha) (Binary To (Binary To (alpha) (alpha)) (alpha)),
    Binary To (alpha) (Binary To (alpha) (alpha)),
    Binary To (Binary To (alpha) (Binary To (alpha) (alpha))) (Binary To (Binary To (alpha) (Binary To (Binary To (alpha) (alpha)) (alpha))) (Binary To (alpha) (alpha))),
    Binary To (Binary To (alpha) (Binary To (Binary To (alpha) (alpha)) (alpha))) (Binary To (alpha) (alpha)),
    Binary To (alpha) (alpha),
    Binary To (Binary To (alpha) (alpha)) (Binary To (Binary To (alpha) (Binary To (alpha) (Binary To (Neg (beta)) (alpha)))) (Binary To (alpha) (Binary To (Neg (beta)) (alpha)))),
    Binary To (Binary To (alpha) (Binary To (alpha) (Binary To (Neg (beta)) (alpha)))) (Binary To (alpha) (Binary To (Neg (beta)) (alpha))),
    Binary To (alpha) (Binary To (Neg (beta)) (alpha)),
    Binary To (Binary To (Binary To (Neg (beta)) (alpha)) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta))))) (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (alpha)) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta)))))),
    Binary To (Binary To (Neg (beta)) (alpha)) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta)))),
    Binary To (alpha) (Binary To (Binary To (Neg (beta)) (alpha)) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta))))),
    Binary To (Binary To (alpha) (Binary To (Neg (beta)) (alpha))) (Binary To (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (alpha)) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta)))))) (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta)))))),
    Binary To (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (alpha)) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta)))))) (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta))))),
    Binary To (alpha) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta)))),
    Binary To (Binary To (alpha) (Binary To (Neg (beta)) (Neg (alpha)))) (Binary To (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta))))) (Binary To (alpha) (Neg (Neg (beta))))),
    Binary To (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta))))) (Binary To (alpha) (Neg (Neg (beta)))),
    Binary To (alpha) (Neg (Neg (beta))),
    Binary To (Binary To (Neg (Neg (beta))) (beta)) (Binary To (alpha) (Binary To (Neg (Neg (beta))) (beta))),
    Binary To (Neg (Neg (beta))) (beta),
    Binary To (alpha) (Binary To (Neg (Neg (beta))) (beta)),
    Binary To (Binary To (alpha) (Neg (Neg (beta)))) (Binary To (Binary To (alpha) (Binary To (Neg (Neg (beta))) (beta))) (Binary To (alpha) (beta))),
    Binary To (Binary To (alpha) (Binary To (Neg (Neg (beta))) (beta))) (Binary To (alpha) (beta)),
    Binary To (alpha) (beta),
    Binary To (beta) (Binary To (Binary To (beta) (beta)) (beta)),
    Binary To (beta) (Binary To (beta) (beta)),
    Binary To (Binary To (beta) (Binary To (beta) (beta))) (Binary To (Binary To (beta) (Binary To (Binary To (beta) (beta)) (beta))) (Binary To (beta) (beta))),
    Binary To (Binary To (beta) (Binary To (Binary To (beta) (beta)) (beta))) (Binary To (beta) (beta)),
    Binary To (beta) (beta),
    Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (beta) (beta)) (Binary To (Binary Or (alpha) (beta)) (beta))),
    Binary To (Binary To (beta) (beta)) (Binary To (Binary Or (alpha) (beta)) (beta)),
    Binary To (Binary Or (alpha) (beta)) (beta),
    Binary To (Neg (beta)) (Binary To (Binary Or (alpha) (beta)) (Neg (beta))),
    Neg (beta),
    Binary To (Binary Or (alpha) (beta)) (Neg (beta)),
    Binary To (Binary To (Binary Or (alpha) (beta)) (beta)) (Binary To (Binary To (Binary Or (alpha) (beta)) (Neg (beta))) (Neg (Binary Or (alpha) (beta)))),
    Binary To (Binary To (Binary Or (alpha) (beta)) (Neg (beta))) (Neg (Binary Or (alpha) (beta))),
    Neg (Binary Or (alpha) (beta))
  ]

proofToAB alpha beta           = --[Var ("PROOF " ++ show alpha       ++ ", " ++ show beta       ++ "|-" ++ show (Binary To alpha beta))]
  [
    Binary To (beta) (Binary To (alpha) (beta)),
    beta,
    Binary To (alpha) (beta)
  ]

proofToNegAB alpha beta        = --[Var ("PROOF " ++ show (Neg alpha) ++ ", " ++ show beta       ++ "|-" ++ show (Binary To alpha beta))]
  proofToAB alpha beta

proofToNegANegB alpha beta     = --[Var ("PROOF " ++ show (Neg alpha) ++ ", " ++ show (Neg beta) ++ "|-" ++ show (Binary To alpha beta))]
  [
    Neg (alpha),
    Neg (beta),
    Binary To (Binary To (alpha) (Binary To (Neg (beta)) (alpha))) (Binary To (alpha) (Binary To (alpha) (Binary To (Neg (beta)) (alpha)))),
    Binary To (alpha) (Binary To (Neg (beta)) (alpha)),
    Binary To (alpha) (Binary To (alpha) (Binary To (Neg (beta)) (alpha))),
    Binary To (alpha) (Binary To (Binary To (alpha) (alpha)) (alpha)),
    Binary To (alpha) (Binary To (alpha) (alpha)),
    Binary To (Binary To (alpha) (Binary To (alpha) (alpha))) (Binary To (Binary To (alpha) (Binary To (Binary To (alpha) (alpha)) (alpha))) (Binary To (alpha) (alpha))),
    Binary To (Binary To (alpha) (Binary To (Binary To (alpha) (alpha)) (alpha))) (Binary To (alpha) (alpha)),
    Binary To (alpha) (alpha),
    Binary To (Binary To (alpha) (alpha)) (Binary To (Binary To (alpha) (Binary To (alpha) (Binary To (Neg (beta)) (alpha)))) (Binary To (alpha) (Binary To (Neg (beta)) (alpha)))),
    Binary To (Binary To (alpha) (Binary To (alpha) (Binary To (Neg (beta)) (alpha)))) (Binary To (alpha) (Binary To (Neg (beta)) (alpha))),
    Binary To (alpha) (Binary To (Neg (beta)) (alpha)),
    Binary To (Binary To (Neg (alpha)) (Binary To (Neg (beta)) (Neg (alpha)))) (Binary To (alpha) (Binary To (Neg (alpha)) (Binary To (Neg (beta)) (Neg (alpha))))),
    Binary To (Neg (alpha)) (Binary To (Neg (beta)) (Neg (alpha))),
    Binary To (alpha) (Binary To (Neg (alpha)) (Binary To (Neg (beta)) (Neg (alpha)))),
    Binary To (Neg (alpha)) (Binary To (alpha) (Neg (alpha))),
    Neg (alpha),
    Binary To (alpha) (Neg (alpha)),
    Binary To (Binary To (alpha) (Neg (alpha))) (Binary To (Binary To (alpha) (Binary To (Neg (alpha)) (Binary To (Neg (beta)) (Neg (alpha))))) (Binary To (alpha) (Binary To (Neg (beta)) (Neg (alpha))))),
    Binary To (Binary To (alpha) (Binary To (Neg (alpha)) (Binary To (Neg (beta)) (Neg (alpha))))) (Binary To (alpha) (Binary To (Neg (beta)) (Neg (alpha)))),
    Binary To (alpha) (Binary To (Neg (beta)) (Neg (alpha))),
    Binary To (Binary To (Binary To (Neg (beta)) (alpha)) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta))))) (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (alpha)) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta)))))),
    Binary To (Binary To (Neg (beta)) (alpha)) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta)))),
    Binary To (alpha) (Binary To (Binary To (Neg (beta)) (alpha)) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta))))),
    Binary To (Binary To (alpha) (Binary To (Neg (beta)) (alpha))) (Binary To (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (alpha)) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta)))))) (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta)))))),
    Binary To (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (alpha)) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta)))))) (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta))))),
    Binary To (alpha) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta)))),
    Binary To (Binary To (alpha) (Binary To (Neg (beta)) (Neg (alpha)))) (Binary To (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta))))) (Binary To (alpha) (Neg (Neg (beta))))),
    Binary To (Binary To (alpha) (Binary To (Binary To (Neg (beta)) (Neg (alpha))) (Neg (Neg (beta))))) (Binary To (alpha) (Neg (Neg (beta)))),
    Binary To (alpha) (Neg (Neg (beta))),
    Binary To (Binary To (Neg (Neg (beta))) (beta)) (Binary To (alpha) (Binary To (Neg (Neg (beta))) (beta))),
    Binary To (Neg (Neg (beta))) (beta),
    Binary To (alpha) (Binary To (Neg (Neg (beta))) (beta)),
    Binary To (Binary To (alpha) (Neg (Neg (beta)))) (Binary To (Binary To (alpha) (Binary To (Neg (Neg (beta))) (beta))) (Binary To (alpha) (beta))),
    Binary To (Binary To (alpha) (Binary To (Neg (Neg (beta))) (beta))) (Binary To (alpha) (beta)),
    Binary To (alpha) (beta)
  ]

proofNegToANegB alpha beta     = --[Var ("PROOF " ++ show alpha       ++ ", " ++ show (Neg beta) ++ "|-" ++ show (Neg (Binary To alpha beta)))]
  [
    alpha,
    Neg (beta),
    Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (beta))) (Binary To (alpha) (beta))),
    Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (beta))),
    Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (beta))) (Binary To (alpha) (beta)))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (beta)))),
    Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (beta))) (Binary To (alpha) (beta)))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (beta))),
    Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (beta)),
    Binary To (alpha) (Binary To (Binary To (alpha) (beta)) (alpha)),
    alpha,
    Binary To (Binary To (alpha) (beta)) (alpha),
    Binary To (Binary To (Binary To (alpha) (beta)) (alpha)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (beta))) (Binary To (Binary To (alpha) (beta)) (beta))),
    Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (beta))) (Binary To (Binary To (alpha) (beta)) (beta)),
    Binary To (Binary To (alpha) (beta)) (beta),
    Binary To (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))),
    Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta))))),
    Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))),
    Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Neg (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Neg (beta))))),
    Binary To (Neg (beta)) (Binary To (Neg (beta)) (Neg (beta))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Neg (beta)))),
    Binary To (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))) (Binary To (Neg (beta)) (Neg (beta))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))) (Binary To (Neg (beta)) (Neg (beta)))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))) (Binary To (Neg (beta)) (Neg (beta)))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))) (Binary To (Neg (beta)) (Neg (beta))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Neg (beta))))) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))) (Binary To (Neg (beta)) (Neg (beta)))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))) (Binary To (Neg (beta)) (Neg (beta)))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))) (Binary To (Neg (beta)) (Neg (beta)))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))) (Binary To (Neg (beta)) (Neg (beta))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))) (Binary To (Neg (beta)) (Neg (beta)))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta))))) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))) (Binary To (Neg (beta)) (Neg (beta))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Neg (beta))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Neg (beta)))) (Binary To (Neg (beta)) (Neg (beta))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Neg (beta)))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Neg (beta))),
    Binary To (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))))),
    Binary To (Binary To (Neg (beta)) (Neg (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Neg (beta)))) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Neg (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))),
    Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta)))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (alpha) (beta)) (beta))) (Binary To (Binary To (alpha) (beta)) (beta))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (alpha) (beta)) (beta))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (alpha) (beta)) (beta)))) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (alpha) (beta)) (beta))) (Binary To (Binary To (alpha) (beta)) (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (alpha) (beta)) (beta)))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (alpha) (beta)) (beta))) (Binary To (Binary To (alpha) (beta)) (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (alpha) (beta)) (beta))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (alpha) (beta)) (beta)),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (alpha) (beta)) (beta))) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta)))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta))),
    Binary To (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))),
    Binary To (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta)))) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))))) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))),
    Binary To (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta)))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta))))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta)))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))))) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta))))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta))))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta)))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta)))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta)))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta)))))) (Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (beta)) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta)))),
    Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta))),
    Neg (beta),
    Neg (Binary To (alpha) (beta))
  ]

excludingThird :: Expression -> [Expression]
excludingThird alpha =
  contraposition alpha (Binary Or alpha (Neg alpha)) ++
  contraposition (Neg alpha) (Binary Or alpha (Neg alpha)) ++
  [
    Binary To (Binary To (Neg (Binary Or (alpha) (Neg (alpha)))) (Neg (alpha))) (Binary To (Binary To (Neg (Binary Or (alpha) (Neg (alpha)))) (Neg (Neg (alpha)))) (Neg (Neg (Binary Or (alpha) (Neg (alpha)))))),
    Binary To (Binary To (Neg (Binary Or (alpha) (Neg (alpha)))) (Neg (Neg (alpha)))) (Neg (Neg (Binary Or (alpha) (Neg (alpha))))),
    Neg (Neg (Binary Or (alpha) (Neg (alpha)))),
    Binary To (Neg (Neg (Binary Or (alpha) (Neg (alpha))))) (Binary Or (alpha) (Neg (alpha))),
    Binary Or (alpha) (Neg (alpha))
  ]

contraposition :: Expression -> Expression -> [Expression]
contraposition alpha beta =
    [
        Binary To (alpha) (beta),
        Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha))),
        Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha))))),
        Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))),
        Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (beta))),
        Binary To (Neg (beta)) (Binary To (alpha) (beta)),
        Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))),
        Binary To (Binary To (Neg (beta)) (Binary To (alpha) (beta))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha))))),
        Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))),
        Binary To (Neg (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha))),
        Binary To (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Neg (beta)) (Neg (alpha)))),
        Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Neg (beta)) (Neg (alpha))),
        Binary To (Neg (beta)) (Neg (alpha))
    ]
