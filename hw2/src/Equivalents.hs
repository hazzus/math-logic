module Equivalents where

import Syntax
import Info

equivalentAxiom :: Expression -> Int -> [Expression]
equivalentAxiom expr num =
  if num /= 10
    then [
            expr,
            Binary To (expr) (Binary To (Neg (expr)) (expr)),
            Binary To (Neg (expr)) (expr),
            Binary To (Neg (expr)) (Binary To (Neg (expr)) (Neg (expr))),
            Binary To (Neg (expr)) (Binary To (Binary To (Neg (expr)) (Neg (expr))) (Neg (expr))),
            Binary To (Binary To (Neg (expr)) (Binary To (Neg (expr)) (Neg (expr)))) (Binary To (Binary To (Neg (expr)) (Binary To (Binary To (Neg (expr)) (Neg (expr))) (Neg (expr)))) (Binary To (Neg (expr)) (Neg (expr)))),
            Binary To (Binary To (Neg (expr)) (Binary To (Binary To (Neg (expr)) (Neg (expr))) (Neg (expr)))) (Binary To (Neg (expr)) (Neg (expr))),
            Binary To (Neg (expr)) (Neg (expr)),
            Binary To (Binary To (Neg (expr)) (expr)) (Binary To (Binary To (Neg (expr)) (Neg (expr))) (Neg (Neg (expr)))),
            Binary To (Binary To (Neg (expr)) (Neg (expr))) (Neg (Neg (expr))),
            Neg (Neg (expr))
         ]
    else
      case expr of
        Binary To (Neg (Neg alpha)) _  ->
          [Binary To alpha (Binary To (Neg (Neg alpha)) alpha)] ++ (contraposition alpha (Binary To (Neg (Neg alpha)) alpha)) ++
          [Binary To (Neg alpha) (Binary To (Neg (Neg alpha)) alpha)] ++ (contraposition (Neg alpha) (Binary To (Neg (Neg alpha)) alpha)) ++
          [
            Binary To (Binary To (Neg (Binary To (Neg (Neg (alpha))) (alpha))) (Neg (alpha))) (Binary To (Binary To (Neg (Binary To (Neg (Neg (alpha))) (alpha))) (Neg (Neg (alpha)))) (Neg (Neg (Binary To (Neg (Neg (alpha))) (alpha))))),
            Binary To (Binary To (Neg (Binary To (Neg (Neg (alpha))) (alpha))) (Neg (Neg (alpha)))) (Neg (Neg (Binary To (Neg (Neg (alpha))) (alpha)))),
            Neg (Neg (Binary To (Neg (Neg (alpha))) (alpha)))
          ]
        _ -> undefined


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



-- please do not ban me, this code was generated by deduction theorem, it's code is in Deduction.hs
-- I can provide actual proof that was deducted into this piece of code
equivalentModusPonens :: Expression -> Maybe Expression -> [Expression]
equivalentModusPonens _  Nothing = undefined
equivalentModusPonens beta (Just alpha) =
  [
    Neg (Neg alpha),
    Neg (Neg (Binary To (alpha) (beta))),
    Binary To (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta)))) (Binary To (Binary To (Neg (beta)) (Neg (Neg (Binary To (alpha) (beta))))) (Neg (Neg (beta)))),
    Binary To (Binary To (Binary To (alpha) (beta)) (Neg (alpha))) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))) (Neg (Binary To (alpha) (beta)))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (alpha))) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (alpha))) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))) (Neg (Binary To (alpha) (beta)))))),
    Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (alpha))) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))) (Neg (Binary To (alpha) (beta))))),
    Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta))),
    Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))),
    Binary To (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))),
    Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))),
    Binary To (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))),
    Binary To (Binary To (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))))),
    Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))))),
    Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))),
    Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta))))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta))))))),
    Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (beta)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta))))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta))))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (beta))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta))))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))))),
    Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta)))))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Neg (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta))))),
    Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))),
    Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha))),
    Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha))))),
    Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))),
    Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Binary To (alpha) (beta)) (Neg (alpha)))),
    Binary To (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Binary To (alpha) (beta)) (Neg (alpha))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Binary To (alpha) (beta)) (Neg (alpha)))))),
    Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Binary To (alpha) (beta)) (Neg (alpha))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta))))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Binary To (alpha) (beta)) (Neg (alpha)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Binary To (alpha) (beta)) (Neg (alpha)))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (alpha) (Neg (beta)))) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Binary To (alpha) (beta)) (Neg (alpha)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Binary To (alpha) (beta)) (Neg (alpha))))),
    Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Binary To (alpha) (beta)) (Neg (alpha)))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha))))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Binary To (alpha) (beta)) (Neg (alpha))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (alpha))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Binary To (Binary To (alpha) (Neg (beta))) (Neg (alpha)))) (Binary To (Binary To (alpha) (beta)) (Neg (alpha))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (alpha)))),
    Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (alpha))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (alpha)))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (alpha))) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))) (Neg (Binary To (alpha) (beta)))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (alpha))) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))) (Neg (Binary To (alpha) (beta)))))) (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))) (Neg (Binary To (alpha) (beta))))),
    Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))) (Neg (Binary To (alpha) (beta)))),
    Binary To (Neg (Neg (alpha))) (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))),
    Binary To (Binary To (Neg (Neg (alpha))) (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha))))) (Binary To (Neg (beta)) (Binary To (Neg (Neg (alpha))) (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))))),
    Binary To (Neg (beta)) (Binary To (Neg (Neg (alpha))) (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha))))),
    Binary To (Neg (Neg (alpha))) (Binary To (Neg (beta)) (Neg (Neg (alpha)))),
    Binary To (Neg (beta)) (Neg (Neg (alpha))),
    Binary To (Binary To (Neg (beta)) (Neg (Neg (alpha)))) (Binary To (Binary To (Neg (beta)) (Binary To (Neg (Neg (alpha))) (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Neg (Neg (alpha))) (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))))) (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha))))),
    Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha))))) (Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta))))),
    Binary To (Binary To (Neg (beta)) (Binary To (Binary To (Binary To (alpha) (beta)) (Neg (Neg (alpha)))) (Neg (Binary To (alpha) (beta))))) (Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta)))),
    Binary To (Neg (beta)) (Neg (Binary To (alpha) (beta))),
    Binary To (Binary To (Neg (beta)) (Neg (Neg (Binary To (alpha) (beta))))) (Neg (Neg (beta))),
    Binary To (Neg (Neg (Binary To (alpha) (beta)))) (Binary To (Neg (beta)) (Neg (Neg (Binary To (alpha) (beta))))),
    Binary To (Neg (beta)) (Neg (Neg (Binary To (alpha) (beta)))),
    Neg (Neg (beta))
  ]
