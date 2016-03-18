#lang racket

#|

<top> ::= <def>* <exp>*

<def> ::= (define [<var> : <type>] <exp>)

<exp> ::= <var>
       |  <literal>
       |  <prim>
       |  (quote <literal>)
       |  (λ <label> [<var> : <type>] : <type> <exp>)
       |  (if <exp> <exp> <exp>)
       |  (let ([<var> : <type>] <exp>) <body>)
       |  (<exp> <exp>)

<literal> ::= int | bool | symbol
<prim> ::= + | - | * | / | >= | <= | > | < | = | and | or | not

<label> ::= symbol

=============

<type> ::= int | bool | symbol
         | (-> <type> <type>)
         | (int <predicate>) | (bool <predicate>) | (symbol <predicate>)

<predicate> ::= #t | (<pred-op> <operand> <operand>)
<pred-op> ::= > | < | = | >= | <= | and | or | not
<operand> ::= <predicate> | <literal> | <var>

|#

(λ 'plus1 [x : (int (>= x 0))] : [y : (int (> y x))]
  (+ x 1))
