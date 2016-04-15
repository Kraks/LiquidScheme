#lang racket

(require rackunit)
(require "structs.rkt")

; TODO inline/expand

(define (int+ l r)
  (match* (l r)
    [((IntValue p1) (IntValue p2)) (pred+ p1 p2)]
    [(_ _) (error 'int+ "not an integer")]))

(define (swap/pand p)
  (match p [(PAnd l r) (PAnd r l)]))

(define (norm/pand p)
  (match p
    ; (int & _ > int)
    [(PAnd (? number? l-num) (PGreater (PSelf) (? number? r-num)))
     (check-true (>= l-num r-num))
     l-num]
    ; (int & _ < int)
    [(PAnd (? number? l-num) (PGreater (? number? r-num) (PSelf)))
     (check-true (<= l-num r-num))
     l-num]
    ; (_ > _ & int) -> (int & _ > _)
    [(PAnd (PGreater _ _) (? number?)) (norm/pand (swap/pand p))]
    ; (_ > int & _ > int)
    [(PAnd (PGreater (PSelf) (? number? l-num)) (PGreater (PSelf) (? number? r-num)))
     (PGreater (PSelf) (max l-num r-num))]
    ; (_ < int & _ < int)
    [(PAnd (PGreater (? number? l-num) (PSelf)) (PGreater (? number? r-num) (PSelf)))
     (PGreater (min l-num r-num) (PSelf))]
    ; (_ > int & _ < int)
    [(PAnd (PGreater (PSelf) (? number? l-num)) (PGreater (? number? r-num) (PSelf)))
     (check-true (<= l-num r-num))
     (if (= l-num r-num) l-num p)]
    ; (_ < int & _ > int)
    [(PAnd (PGreater (? number?) (PSelf)) (PGreater (PSelf) (? number?)))
     (norm/pand (swap/pand p))]
    ; ((_ > int & _ < int) & (_ > int & _ < int))
    [(PAnd (PAnd (PGreater (PSelf) (? number? l1))
                 (PGreater (? number? r1) (PSelf)))
           (PAnd (PGreater (PSelf) (? number? l2))
                 (PGreater (? number? r2) (PSelf))))
     (norm/pand (PAnd (PGreater (PSelf) (max l1 l2))
                      (PGreater (min r1 r2) (PSelf))))]
    ; (pand & pand)
    [(PAnd (? PAnd? l) (? PAnd? r))
     (norm/pand (PAnd (norm/pand l) (norm/pand r)))]
    [p p]))

(define (pred+ l r)
  (match* (l r)
    [(#t _) #t]
    [(_ #t) #t]
    ;;;;;;;;;;;;;;;;
    [((? number?) (? number?)) (+ l r)]
    [((? number?) (PGreater (PSelf) (? number? r-num)))
     (PGreater (PSelf) (+ l r-num))]
    [((? number?) (PGreater (? number? r-num) (PSelf)))
     (PGreater (+ l r-num) (PSelf))]
    [((? number?) (? PAnd?))
     (match (norm/pand r)
       [(PAnd (PGreater (PSelf) (? number? l-num)) (PGreater (? number? r-num) (PSelf)))
        (PAnd (PGreater (PSelf) (+ l l-num)) (PGreater (+ l r-num) (PSelf)))]
       [r (pred+ l r)])]
    [((? number?) (POr p1 p2))
     (POr (pred+ l p1) (pred+ l p2))]
    [((? number?) (PNot p))
     (PNot (pred+ l p))]
    [((PGreater _ _) (? number?)) (pred+ r l)]
    [((PAnd _ _) (? number?)) (pred+ r l)]
    [((POr _ _) (? number?)) (pred+ r l)]
    [((PNot _) (? number?)) (pred+ r l)]
    ;;;;;;;;;;;;;;;;
    [((PGreater (PSelf) (? number? l-num)) (PGreater (PSelf) (? number? r-num)))
     (PGreater (PSelf) (+ l-num r-num))]
    [((PGreater (PSelf) (? number? l-num)) (PGreater (? number? r-num) (PSelf)))
     #t]
    [((PGreater (? number? l-num) (PSelf)) (PGreater (? number? r-num) (PSelf)))
     (PGreater (+ l-num r-num) (PSelf))]
    [((PGreater (? number?) (PSelf)) (PGreater (PSelf) _))
     (pred+ r l)]
    [((PGreater (PSelf) (? number? l-num)) (? PAnd?))
     (match (norm/pand r)
       [(PAnd (PGreater (PSelf) (? number? p-l-num)) (PGreater (? number? p-r-num) (PSelf)))
        (PAnd (PGreater (PSelf) (+ l-num p-l-num)) (PGreater (+ l-num p-r-num) (PSelf)))]
       [r (pred+ l r)])]
    [((PGreater (? number? l-num) (PSelf)) (? PAnd?))
     (match (norm/pand r)
       [(PAnd (PGreater (PSelf) (? number? p-l-num)) (PGreater (? number? p-r-num) (PSelf)))
        (PGreater (+ l-num p-r-num) (PSelf))]
       [r (pred+ l r)])]
    [((PGreater _ _) (POr p1 p2))
     (POr (pred+ l p1) (pred+ l p2))]
    [((PGreater _ _) (PNot p))
     (PNot (pred+ l p))]
    [((PAnd _ _) (PGreater _ _)) (pred+ r l)]
    [((POr _ _) (PGreater _ _)) (pred+ r l)]
    [((PNot _) (PGreater _ _)) (pred+ r l)]
    ;;;;;;;;;;;;;;;;
    [((PAnd _ _) (PAnd _ _))
     (match* ((norm/pand l) (norm/pand r))
       [((PAnd (PGreater (PSelf) (? number? l1)) (PGreater (? number? u1) (PSelf)))
         (PAnd (PGreater (PSelf) (? number? l2)) (PGreater (? number? u2) (PSelf))))
        (PAnd (PGreater (PSelf) (+ l1 l2)) (PGreater (+ u1 u2) (PSelf)))]
       [(pl pr) (pred+ pl pr)])]
    [((PAnd p11 p12) (POr p21 p22)) -1]
    [((PAnd p11 p12) (PNot p)) -1]
    [((POr _ _) (PAnd _ _)) (pred+ r l)]
    [((PNot _) (PAnd _ _)) (pred+ r l)]
    ;;;;;;;;;;;;;;;;
    [((POr p11 p12) (POr p21 p22)) -1]
    [((POr p11 p12) (PNot p)) -1]
    [((PNot _) (POr _ _)) (pred+ r l)]
    ;;;;;;;;;;;;;;;;
    [((PNot p1) (PNot p2)) #t]
    [(_ _) (error 'pred+ "unknown predicate ~a ~a" l r)]))

(module+ test
  (pred+ #t 3)
  (pred+ 3 #t)
  (pred+ 3 4)
  (pred+ 4 (PGreater (PSelf) 5))
  (pred+ -4 (PGreater 5 (PSelf)))
  (pred+ (PGreater (PSelf) 3) 5)
  (pred+ (PGreater 3 (PSelf)) 5)
  (pred+ 3 (PAnd (PGreater (PSelf) 1) (PGreater (PSelf) 4)))
  (pred+ (PGreater (PSelf) 3) (PGreater (PSelf) 5))
  (pred+ (PGreater (PSelf) 3) (PGreater 5 (PSelf)))
  (pred+ (PGreater 3 (PSelf)) (PGreater 3 (PSelf)))
  (pred+ (PGreater 3 (PSelf)) (PGreater (PSelf) 5))
  (pred+ (PAnd 3 (PGreater (PSelf) 2)) (PAnd (PGreater (PSelf) 5) 10))
  (pred+ (PGreater (PSelf) 5) (PAnd (PGreater (PSelf) 6) (PGreater 8 (PSelf))))
  (pred+ (PGreater (PSelf) 5) (PAnd 5 (PGreater (PSelf) 3)))
  (pred+ (PGreater 5 (PSelf)) (PAnd (PGreater (PSelf) 6) (PGreater 8 (PSelf))))
  (pred+ (PGreater 5 (PSelf)) (PAnd 5 (PGreater (PSelf) 3)))
  (pred+ (PAnd (PAnd (PGreater (PSelf) 1)
                     (PGreater 5 (PSelf)))
               (PAnd (PGreater (PSelf) 3)
                     (PGreater 7 (PSelf))))
         3)
  (pred+ (PAnd (PAnd (PGreater (PSelf) 1)
                     (PGreater 5 (PSelf)))
               (PAnd (PGreater (PSelf) 3)
                     (PGreater 7 (PSelf))))
         (PAnd (PAnd (PGreater (PSelf) 10)
                     (PGreater 15 (PSelf)))
               (PAnd (PGreater (PSelf) 12)
                     (PGreater 17 (PSelf)))))

  (pred+ (PAnd (PAnd (PGreater (PSelf) 3)
                     (PGreater 7 (PSelf)))
               (PAnd (PGreater (PSelf) 1)
                     (PGreater 5 (PSelf))))
         (PAnd (PAnd (PGreater (PSelf) 10)
                     (PGreater 15 (PSelf)))
               (PAnd (PGreater (PSelf) 12)
                     (PGreater 17 (PSelf))))))