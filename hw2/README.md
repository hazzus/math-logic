# hw2

## Glivenko theorem

Input of proggram is correct proof of statement F in classical propositional calculus.  
Grammar is same as previous task.  

Ouput should be proof of !!F in intuitionistic propositional calculus.

### Example
Input :
```
A |- A
A
```
Output:
```
A |- !!A
A
(A -> (!A -> A))
(!A -> A)
(!A -> (!A -> !A))
((!A -> (!A -> !A)) -> ((!A -> ((!A -> !A) -> !A)) -> (!A -> !A)))
((!A -> ((!A -> !A) -> !A)) -> (!A -> !A))
(!A -> ((!A -> !A) -> !A))
(!A -> !A)
((!A -> A) -> ((!A -> !A) -> !!A))
((!A -> !A) -> !!A)
!!A
```
