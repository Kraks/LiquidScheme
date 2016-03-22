#lang racket

(require rackunit)

#|
User Syntax

<top> ::= <def>* <exp>*

<def> ::= (define <var> : <type> <exp>)
       |  (define (<name> [<var> : <type>]) : <type> <exp>)

<exp> ::= <var>
       |  <literal>
       |  <prim>
       |  (λ <label> [<var> : <type>] : <type> <exp>)
       |  (if <exp> <exp> <exp>)
       |  (let ((<var> : <type> <exp>)) <body>)
       |  (<exp> <exp>)

<literal> ::= <int> | <bool>
<prim> ::= + | - | * | / | >= | <= | > | < | = | and | or | not

<label> ::= <symbol>

=============

<type> ::= Int | Bool | Any
         | (-> <type> <type>)
         | (Int <predicate>) | (Bool <predicate>) | (Any #t)

<predicate> ::= #t | (<pred-op> <operand> <operand>)
<pred-op> ::= > | < | = | >= | <= | and | or | not
<operand> ::= <predicate> | <literal> | _

|#

#|
Core Syntax

<top> ::= <def>* <exp>*
<def> ::= (define (<name> [<var> : <type>]) : <type> <exp>)

<exp> ::= <var>
       |  <literal>
       |  <prim>
       |  (λ <label> [<var> : <type>] : <type> <exp>)
       |  (if <exp> <exp> <exp>)
       |  (<exp> <exp>)

<literal> ::= <int> | <bool>
<prim> ::= + | - | * | / | >= | <= | > | < | = | and | or | not

<label> ::= <symbol>

=============

<type> ::= (-> <type> <type>)
         | (Int <predicate>) | (Bool <predicate>) | (Any #t)
<predicate> ::= #t | (<pred-op> <operand> <operand>)
<pred-op> ::= > | < | = | >= | <= | and | or | not
<operand> ::= <predicate> | <literal> | _

|#

; TODO adding Any type?
; TODO type of let body?
; TODO do we really need (quote ...)?

(define (desugar expr)
  (match expr
    [`(define (,name [,var : ,atype]) : ,rtype ,exp)
     ;=>
     `(define ,name : (,(desugar-type atype) -> ,(desugar-type rtype))
        (lambda ,name [,var : ,(desugar-type atype)] : ,(desugar-type rtype) ,(desugar exp)))]
    [`(define ,name : ,type ,exp)
     ;=>
     `(define ,name : ,(desugar-type type) ,(desugar exp))]
    [`(let ((,var : ,type ,exp)) ,body)
     ;=>
     `((lambda ,(gensym 'let) [,var : ,(desugar-type type)] : (Any #t) ,body) ,(desugar exp))]
    [`(,rator ,rand)
     ;=>
     `(,(desugar rator) ,(desugar rand))]
    [e e]))

(define (desugar-type type)
  (match type
    ['Int '(Int #t)]
    ['Bool '(Bool #t)]
    ['Any '(Any #t)]
    [`(,atype -> ,rtype)
     `(,(desugar-type atype) -> ,(desugar-type rtype))]
    [t t]))


(module+ test
  (check-equal? (desugar-type 'Int) '(Int #t))
  (check-equal? (desugar-type 'Bool) '(Bool #t))
  (check-equal? (desugar-type '(Int -> Bool)) '((Int #t) -> (Bool #t)))
  (check-equal? (desugar-type '(Int (> _ 3))) '(Int (> _ 3)))
  (check-equal? (desugar-type '(Bool (and _ #f))) '(Bool (and _ #f)))
  )

(module+ test
  (check-equal? (desugar '(define x : Int 1))
                '(define x : (Int #t) 1))
  (check-equal? (desugar '(define (add1 [x : Int]) : Int (+ x 1)))
                '(define add1 : ((Int #t) -> (Int #t)) (lambda add1 [x : (Int #t)] : (Int #t) (+ x 1))))
  (check-match (desugar '(let ((x : Int 3)) (+ x 1)))
               `((lambda ,sym (x : (Int #t)) : (Any #t) (+ x 1)) 3))
  )