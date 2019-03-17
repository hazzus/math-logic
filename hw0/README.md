# hw0

Parsing logical expressions

Given file has such grammar:

⟨File⟩ ::= ⟨Expr⟩
⟨Expr⟩ ::= ⟨Disj⟩ | ⟨Disj⟩ ‘->’ ⟨Expr⟩
⟨Disj⟩ ::= ⟨Conj⟩ | ⟨Disj⟩ ‘|’  ⟨Conj⟩
⟨Conj⟩ ::= ⟨Neg⟩  | ⟨Conj⟩ ‘&’  ⟨Neg⟩
⟨Neg⟩  ::= ‘!’ ⟨Neg⟩ | ⟨Var⟩ | ‘(’ ⟨Expr⟩ ‘)’
⟨Var⟩  ::= (‘A’ . . . ‘Z’) {‘A’ . . . ‘Z’ | ‘0’ . . . ‘9’ | ‘’’}

Names doesn't contain spaces. There is no spaces between '->' operator symbols. Other places may contain spaces.  
Symbols tab and \r must be readed as spaces.

The task is to parse expressiong, build and output it's syntax tree in new grammar:

⟨File⟩ ::= ⟨Vertex⟩
⟨Vertex⟩ ::= ‘(’ ⟨Symbol⟩ ‘,’ ⟨Vertex⟩ ‘,’ ⟨Vertex⟩ ‘)’
| ‘(!’⟨Vertex⟩‘)’
| ⟨Var⟩
⟨Symbol⟩ ::= ‘->’ | ‘|’ | ‘&’
⟨Var⟩ ::= (‘A’ . . . ‘Z’) {‘A’ . . . ‘Z’ | ‘0’ . . . ‘9’ | ‘’’}*

Examples:

| Input | Ouput |
| ----- | ----- |
| "!A&!B->!(A |B)"      |  "(->,(&,(!A),(!B)),(!( |,A,B))) "    |
| "P1'->!QQ->!R10&S   |!T&U&V"  | "(->,P1',(->,(!QQ),(  |,(&,(!R10),S),(&,(&,(!T),U),V))))"  |
