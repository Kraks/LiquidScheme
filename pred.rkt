#lang racket

(require "structs.rkt")

; TODO inline/expand

(define (int+ l r)
  (match* (l r)
    [((IntValue p1) (IntValue p2)) (pred+ p1 p2)]
    [(_ _) (error 'int+ "not an integer")]))

(define (pred+ l r)
  (match* (l r)
    [((? number?) (? number?)) (IntValue (+ l r))]
    [((? number?) (PGreater (PSelf) (? number? r-num)))
     (IntValue (PGreater (PSelf) (+ l r-num)))]
    [((? number?) (PGreater (? number? r-num) (PSelf)))
     (IntValue (PGreater (+ l r-num) (PSelf)))]
    [((? number?) (PAnd p1 p2))
     (IntValue (PAnd (pred+ l p1) (pred+ l p2)))]
    [((? number?) (POr p1 p2))
     (IntValue (POr (pred+ l p1) (pred+ l p2)))]
    [((? number?) (PNot p))
     (IntValue (PNot (pred+ l p)))]
    [((PGreater _ _) (? number?)) (pred+ r l)]
    [((PAnd _ _) (? number?)) (pred+ r l)]
    [((POr _ _) (? number?)) (pred+ r l)]
    [((PNot _) (? number?)) (pred+ r l)]
    ;;;;;;;;;;;;;;;;
    [((PGreater (PSelf) (? number? l-num)) (PGreater (PSelf) (? number? r-num)))
     (IntValue (PGreater (PSelf) (+ l-num r-num)))]
    [((PGreater (PSelf) (? number? l-num)) (PGreater (? number? r-num) (PSelf)))
     (IntValue #t)]
    [((PGreater (? number? l-num) (PSelf)) (PGreater (? number? r-num) (PSelf)))
     (IntValue (PGreater (+ l-num r-num) (PSelf)))]
    [((PGreater (? number?) (PSelf)) (PGreater (PSelf) _))
     (pred+ r l)]
    [((PGreater _ _) (PAnd p1 p2))
     (PAnd (pred+ l p1) (pred+ l p2))]
    [((PGreater _ _) (POr p1 p2))
     (POr (pred+ l p1) (pred+ l p2))]
    [((PGreater _ _) (PNot p))
     (PNot (pred+ l p))]
    [((PAnd _ _) (PGreater _ _)) (pred+ r l)]
    [((POr _ _) (PGreater _ _)) (pred+ r l)]
    [((PNot _) (PGreater _ _)) (pred+ r l)]
    ;;;;;;;;;;;;;;;;
    [((PAnd p11 p12) (PAnd p21 p22)) ...]
    [((PAnd p11 p12) (POr p21 p22)) ...]
    [((PAnd p11 p12) (PNot p)) ...]
    [((POr _ _) (PAnd _ _)) (pred+ r l)]
    [((PNot _) (PAnd _ _)) (pred+ r l)]
    ;;;;;;;;;;;;;;;;
    [((POr p11 p12) (POr p21 p22)) ...]
    [((POr p11 p12) (PNot p)) ...]
    [((PNot _) (POr _ _)) (pred+ r l)]
    ;;;;;;;;;;;;;;;;
    [((PNot p1) (PNot p2)) (IntValue #t)]
    [(_ _) (error 'pred+ "unknown predicate ~a ~a" l r)]))
     
(pred+ 3 4)
(pred+ 4 (PGreater (PSelf) 5))
(pred+ -4 (PGreater 5 (PSelf)))
(pred+ 3 (PAnd (PGreater (PSelf) 1) (PGreater (PSelf) 4)))