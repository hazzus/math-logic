# hw1

## Minimization of proof

Input is a proof of expression in next grammar:
```
⟨File⟩ ::= ⟨Context⟩ ‘|-’ ⟨Expr⟩ ‘\n’ ⟨Line⟩*
⟨Context⟩ ::= ⟨Expr⟩ [‘,’ ⟨Expr⟩]*
| ‘’
⟨Line⟩ ::= ⟨Expr⟩ ‘\n’
⟨Expr⟩ ::= ⟨Expr⟩ ‘&’ ⟨Expr⟩
| ⟨Expr⟩ ‘ |’ ⟨Expr⟩
| ⟨Expr⟩ ‘->’ ⟨Expr⟩
| ‘!’ ⟨Expr⟩
| ‘(’ ⟨Expr⟩ ‘)’
| ⟨Var⟩
⟨Var⟩ ::= (‘A’ . . . ‘Z’) {‘A’ . . . ‘Z’ | ‘0’ . . . ‘9’ | ‘'’}*
```

Operators '&' and '|' are left-associative. Operator '->' id right-associative.   
Operators priority: '!', '&', '|', '->'.  

Variable names doesn't contain spaces. There is no spaces between operator's symbols '|-' and '->'.  
In other case there can be spaces. Tabulation and '\r' must be read as spaces.

The task is to check proof on correctness. If it's incorrect the output should be "Proof is incorrect". Else programm should minimize and annotate the proof.  
Minimization is new proof so that:  
* New proof proofs same expression as input proof
* Lines of new proof are subsequence of input proof
* In new proof any expression doesn't meets in many lines.
* New proof doesn't contatin unused expressions, all of expressions, except the last one should be used in Modus Ponens.

Annotation is:
* All lines should be numbered
* Every line should contain explanation, how it was created:
    * Axiom: number of axiom
    * Hypothesis: number of hypothesis
    * Modus Ponens: numbers of used lines.
    
Examples:
------
Input:
```
|- A -> A
A & A -> A
A -> A -> A
A -> (A -> A) -> A
A & A -> A
(A -> A -> A) -> (A -> (A -> A) -> A) -> A -> A
(A -> (A -> A) -> A) -> A -> A
A & A -> A
A -> A
```
Output:
```
|- (A -> A)
[1. Ax. sch. 1] (A -> (A -> A))
[2. Ax. sch. 1] (A -> ((A -> A) -> A))
[3. Ax. sch. 2] ((A -> (A -> A)) -> ((A -> ((A -> A) -> A)) -> (A -> A)))
[4. M.P. 3, 1] ((A -> ((A -> A) -> A)) -> (A -> A))
[5. M.P. 4, 2] (A -> A)
```

-------
Input:
```
A->B, !B |- !A
A->B
!B
!B -> A -> !B
A -> !B
(A -> B) -> (A -> !B) -> !A
(A -> !B) -> !A
!A
```
Output:
```
(A -> B), !B |- !A
[1. Hypothesis 1] (A -> B)
[2. Hypothesis 2] !B
[3. Ax. sch. 1] (!B -> (A -> !B))
[4. M.P. 3, 2] (A -> !B)
[5. Ax. sch. 9] ((A -> B) -> ((A -> !B) -> !A))
[6. M.P. 5, 1] ((A -> !B) -> !A)
[7. M.P. 6, 4] !A
```
-------
Input:
```
A, C |- B’
B’
```
Output:
`Proof is incorrect`
