#lang racket

(require rackunit)
(require "structs.rkt")

(provide int+)

; TODO inline/expand
; TODO DNF/CNF/NNF ?

(define (int+ l r)
  (match* (l r)
    [((IntValue p1) (IntValue p2)) (pred+ p1 p2)]
    [(_ _) (error 'int+ "not an integer")]))

(define (swap/pand p)
  (match p [(PAnd l r) (PAnd r l)]))

(define (norm/por p)
  (match p
    [(POr a b) (PNot (PAnd (PNot (norm/por a)) (PNot (norm/por b))))]
    [p p]))

(define (norm/pnot p)
  (match p
    [(or (? number?) (? True?) (? False?)) p]
    [(PNot (True)) (False)]
    [(PNot (False)) (True)]
    [(PNot (? number?)) p]
    [(PNot (PNot p1)) (norm/pnot p1)]
    [(PNot (? PAnd? pa))
     (match (norm/pand pa)
       [(PAnd (PGreater (PSelf) (? number? l-num)) (PGreater (? number? r-num) (PSelf))) -1]
       [normed (norm/pnot (PNot normed))])]
    
    [(PNot (PGreater (PSelf) (? number? n))) -1]
    [(PNot (PGreater (? number? n) (PSelf))) -1]))

(module+ test
  (check-equal? (norm/pnot (PNot 3)) (PNot 3))
  (check-equal? (norm/pnot (PNot (PNot 3))) 3)
  (check-equal? (norm/pnot (PNot (True))) (False))
  (check-equal? (norm/pnot (PNot (False))) (True))
  (check-equal? (norm/pnot (PNot (PNot (PNot (False))))) (True))
  (check-equal? (norm/pnot (PNot (PNot (PNot (PNot (False)))))) (False)))

(define (norm/pand p)
  (match p
    [(PAnd (True) (True)) (True)]
    [(PAnd (False) _) (False)]
    [(PAnd _ (False)) (False)]

    [(PAnd (? number? l) (? number? r))
     (check-true (= l r))
     l]
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
    
    [(PAnd (PAnd (PGreater (PSelf) (? number? pl))
                 (PGreater (? number? pr) (PSelf)))
           (PGreater (PSelf) (? number? l)))
     (norm/pand (PAnd (PGreater (PSelf) (max l pl)) (PGreater pr (PSelf))))]
    [(PAnd (PAnd (PGreater (PSelf) (? number? pl))
                 (PGreater (? number? pr) (PSelf)))
           (PGreater (? number? u) (PSelf)))
     (norm/pand (PAnd (PGreater (PSelf) pl) (PGreater (min u pr) (PSelf))))]
    
    [(PAnd (? PAnd? l) (? PAnd? r))
     (norm/pand (PAnd (norm/pand l) (norm/pand r)))]
    [(PAnd (PAnd pl pr) r)
     (norm/pand (PAnd (norm/pand (PAnd pl r))
                      (norm/pand (PAnd pr r))))]
    [(PAnd l (? PAnd? r)) (norm/pand (PAnd r l))]

    [(PAnd (? PNot? n1) (? PNot? n2)) (norm/pand (norm/pnot n1) (norm/pnot n2))]
    [(PAnd (? PNot? n) (? number? r))
     (norm/pand (PAnd (norm/pnot n) r))]
    [(PAnd (? PNot? n) (PGreater (PSelf) (? number? r-num))) -1]
    [(PAnd l (? PNot? r)) -1]
    ; TODO
    
    [p (printf "warning: ~a\n" p) p]))

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
     (norm/por (POr (pred+ l p1) (pred+ l p2)))]
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
     (norm/por (POr (pred+ l p1) (pred+ l p2)))]
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
    [((PAnd p11 p12) (POr p21 p22))
     (pred+ (norm/pand l) (norm/por r))]
    [((PAnd p11 p12) (PNot p))
     (match* ((norm/pand l) r)
       [((? PAnd? norm-l) _) (PNot (pred+ norm-l p))]
       [(norm-l _) (pred+ norm-l r)])]
    ;[((POr _ _) (PAnd _ _)) (pred+ r l)]
    [((PNot _) (PAnd _ _)) (pred+ r l)]
    ;;;;;;;;;;;;;;;;
    ;[((POr p11 p12) (POr p21 p22)) -1]
    ;[((POr p11 p12) (PNot p)) -1]
    ;[((PNot _) (POr _ _)) (pred+ r l)]
    ;;;;;;;;;;;;;;;;
    [((PNot p1) (PNot p2)) #t]
    [(_ _) (error 'pred+ "unknown predicate ~a ~a" l r)]))

(module+ test
  (check-equal? (norm/pand (PAnd (PAnd (True) (False)) (PAnd (True) (True))))
                (False))
  (check-equal? (norm/pand (PAnd (PAnd (True) (True)) (PAnd (True) (True))))
                (True))
  (check-equal? (norm/pand (PAnd 5 5))
                5)
  (check-equal? (norm/pand (PAnd 3 (PGreater 6 (PSelf))))
                3)
  (check-equal? (norm/pand (PAnd (PGreater 5 (PSelf)) (PGreater 3 (PSelf))))
                (PGreater 3 (PSelf)))
  (check-equal? (norm/pand (PAnd (PGreater (PSelf) 3) (PGreater 5 (PSelf))))
                (PAnd (PGreater (PSelf) 3) (PGreater 5 (PSelf))))
  (check-equal? (norm/pand (PAnd (PGreater (PSelf) 3) (PGreater 3 (PSelf))))
                3)
  (check-equal? (norm/pand (PAnd 3 (PAnd (PGreater (PSelf) 2) (PGreater 5 (PSelf)))))
                3)
  (check-equal? (norm/pand (PAnd (PGreater 15 (PSelf)) (PGreater (PSelf) 10)))
                (PAnd (PGreater (PSelf) 10) (PGreater 15 (PSelf))))
  (check-equal? (norm/pand (PAnd (PAnd (PGreater (PSelf) 3) (PGreater 5 (PSelf)))
                                 (PAnd (PGreater (PSelf) 5) (PGreater 9 (PSelf)))))
                5)
  (check-equal? (norm/pand (PAnd (PAnd (PAnd (PGreater (PSelf) 0) (PGreater 9 (PSelf)))
                                       (PAnd (PGreater (PSelf) 3) (PGreater 8 (PSelf))))
                                 (PAnd (PGreater (PSelf) 5) (PGreater 9 (PSelf)))))
                (PAnd (PGreater (PSelf) 5) (PGreater 8 (PSelf))))
  (check-equal? (norm/pand (PAnd (PAnd (PGreater (PSelf) 2) (PGreater 9 (PSelf)))
                                 4))
                4)
  (check-equal? (norm/pand (PAnd (PAnd (PGreater (PSelf) 2) (PGreater 9 (PSelf)))
                                 (PGreater (PSelf) 3)))
                (PAnd (PGreater (PSelf) 3) (PGreater 9 (PSelf))))
  (check-equal? (norm/pand (PAnd (PAnd (PGreater (PSelf) 2) (PGreater 9 (PSelf)))
                                 (PGreater 7 (PSelf))))
                (PAnd (PGreater (PSelf) 2) (PGreater 7 (PSelf))))
  (check-equal? (norm/pand (PAnd (PAnd (PGreater 10 (PSelf)) (PGreater (PSelf) 3))
                                 (PAnd (PGreater 11 (PSelf)) (PGreater (PSelf) 4))))
                (PAnd (PGreater (PSelf) 4) (PGreater 10 (PSelf)))))

(module+ test
  (norm/por (POr 8 (PGreater (PSelf) 1))))

(module+ test
  (check-equal? (pred+ #t 3) #t)
  (check-equal? (pred+ 3 #t) #t)
  (check-equal? (pred+ 3 4) 7)
  (check-equal? (pred+ 4 (PGreater (PSelf) 5))
                (PGreater (PSelf) 9))
  (check-equal? (pred+ -4 (PGreater 5 (PSelf)))
                (PGreater 1 (PSelf)))
  (check-equal? (pred+ (PGreater (PSelf) 3) 5)
                (PGreater (PSelf) 8))
  (check-equal? (pred+ (PGreater 3 (PSelf)) 5)
                (PGreater 8 (PSelf)))
  (check-equal? (pred+ 3 (PAnd (PGreater (PSelf) 1) (PGreater (PSelf) 4)))
                (PGreater (PSelf) 7))
  (check-equal? (pred+ (PGreater (PSelf) 3) (PGreater (PSelf) 5))
                (PGreater (PSelf) 8))
  (check-equal? (pred+ (PGreater (PSelf) 3) (PGreater 5 (PSelf)))
                #t)
  (check-equal? (pred+ (PGreater 3 (PSelf)) (PGreater 3 (PSelf)))
                (PGreater 6 (PSelf)))
  (check-equal? (pred+ (PGreater 3 (PSelf)) (PGreater (PSelf) 5))
                #t)
  (check-equal? (pred+ (PAnd 3 (PGreater (PSelf) 2)) (PAnd (PGreater (PSelf) 5) 10))
                13)
  (check-equal? (pred+ (PGreater (PSelf) 5) (PAnd (PGreater (PSelf) 6) (PGreater 8 (PSelf))))
                (PAnd (PGreater (PSelf) 11) (PGreater 13 (PSelf))))
  (check-equal? (pred+ (PGreater (PSelf) 5) (PAnd 5 (PGreater (PSelf) 3)))
                (PGreater (PSelf) 10))
  (check-equal? (pred+ (PGreater 5 (PSelf)) (PAnd (PGreater (PSelf) 6) (PGreater 8 (PSelf))))
                (PGreater 13 (PSelf)))
  (check-equal? (pred+ (PGreater 5 (PSelf)) (PAnd 5 (PGreater (PSelf) 3)))
                (PGreater 10 (PSelf)))
  (check-equal? (pred+ (PAnd (PAnd (PGreater (PSelf) 1)
                                   (PGreater 5 (PSelf)))
                             (PAnd (PGreater (PSelf) 3)
                                   (PGreater 7 (PSelf))))
                       3)
                (PAnd (PGreater (PSelf) 6) (PGreater 8 (PSelf))))
  (check-equal? (pred+ (PAnd (PAnd (PGreater (PSelf) 1)
                                   (PGreater 5 (PSelf)))
                             (PAnd (PGreater (PSelf) 3)
                                   (PGreater 7 (PSelf))))
                       3)
                (PAnd (PGreater (PSelf) 6) (PGreater 8 (PSelf))))

  ;(pred+ 3 (PAnd (PNot 8) (PGreater (PSelf) 1)))
  
  (check-equal? (pred+ (PAnd (PAnd (PGreater (PSelf) 3)
                                   (PGreater 7 (PSelf)))
                             (PAnd (PGreater (PSelf) 1)
                                   (PGreater 5 (PSelf))))
                       (PAnd (PAnd (PGreater (PSelf) 10)
                                   (PGreater 15 (PSelf)))
                             (PAnd (PGreater (PSelf) 12)
                                   (PGreater 17 (PSelf)))))
                (PAnd (PGreater (PSelf) 15) (PGreater 20 (PSelf))))
  
  (check-equal? (pred+ (PAnd (PAnd (PGreater (PSelf) 3)
                                   (PAnd (PGreater (PSelf) 4)
                                         (PGreater 6 (PSelf))))
                             (PAnd (PGreater (PSelf) 1)
                                   (PGreater 5 (PSelf))))
                       (PAnd (PAnd (PGreater (PSelf) 10)
                                   (PGreater 15 (PSelf)))
                             (PAnd (PGreater (PSelf) 12)
                                   (PGreater 17 (PSelf)))))
                (PAnd (PGreater (PSelf) 16) (PGreater 20 (PSelf))))
  
  (check-equal? (pred+ (PNot 3) (PNot 5)) #t))


#;
(define (norm/pand p)
  (match p
    [(PAnd (? number? l-num) (PGreater (PSelf) (? number? r-num)))
     (check-true (>= l-num r-num))
     l-num]
    [(PAnd (? number? l-num) (PGreater (? number? r-num) (PSelf)))
     (check-true (<= l-num r-num))
     l-num]
    [(PAnd (PGreater _ _) (? number?)) (norm/pand (swap/pand p))]
    [(PAnd (PGreater (PSelf) (? number? l-num)) (PGreater (PSelf) (? number? r-num)))
     (PGreater (PSelf) (max l-num r-num))]
    [(PAnd (PGreater (? number? l-num) (PSelf)) (PGreater (? number? r-num) (PSelf)))
     (PGreater (min l-num r-num) (PSelf))]
    [(PAnd (PGreater (PSelf) (? number? l-num)) (PGreater (? number? r-num) (PSelf)))
     (check-true (<= l-num r-num))
     (if (= l-num r-num) l-num p)]
    [(PAnd (PGreater (? number?) (PSelf)) (PGreater (PSelf) (? number?)))
     (norm/pand (swap/pand p))]
    [(PAnd (PAnd (PGreater (PSelf) (? number? l1))
                 (PGreater (? number? r1) (PSelf)))
           (PAnd (PGreater (PSelf) (? number? l2))
                 (PGreater (? number? r2) (PSelf))))
     (norm/pand (PAnd (PGreater (PSelf) (max l1 l2))
                      (PGreater (min r1 r2) (PSelf))))]
    [(PAnd (? PAnd? l) (? PAnd? r))
     (norm/pand (PAnd (norm/pand l) (norm/pand r)))]
    [p p]))
