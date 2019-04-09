# hw3
## Correctness of classical propositional calculus thorem
Input of program is expression in classical propositional calculus.  
It consists of less than _4 unique variables_.

Program creates proof of input expression alpha  
* **Г |- alpha**, where **Г** consists of variables,  
or if it's impossible creates proof  
* **Г |- !alpha**, where **Г** consists of !variables

If proofing is impossible in both ways it gives **:(** as output.
