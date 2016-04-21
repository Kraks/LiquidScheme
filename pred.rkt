#lang racket

(require rackunit)
(require "structs.rkt")

(provide int/+
         int/-
         int/*
         int/eq
         bool/and
         bool/or
         bool/not
         all-bools)

; TODO inline/expand
; !!!! TODO int/+ int/- int/* bool/and bool/or

; is p1 a subset of p2?
; Predicate Predicate -> Predicate
(define (is-sub-pred? p1 p2)
  (match* (p1 p2)
    [((? number? n) (? number? m))
     (= n m)]
    [((? number? n) (PGreater (PSelf) (? number? m)))
     (> n m)]
    [((? number? n) (PGreater (? number? m) (PSelf)))
     (< n m)]
    [((? number? n) (PAnd (PGreater (PSelf) (? number? l))
                          (PGreater (? number? u) (PSelf))))
     (and (>= n l) (<= n u))]
    ;;;;;;;;;;;;;;
    [((PGreater (PSelf) (? number? m)) (? number? n))
     #f]
    [((PGreater (PSelf) (? number? m)) (PGreater (PSelf) (? number? n)))
     (>= m n)]
    [((PGreater (PSelf) (? number? m)) (PGreater (? number? n) (PSelf)))
     #f]
    [((PGreater (PSelf) (? number? m)) (PAnd _ _))
     #f]
    ;;;;;;;;;;;;;;
    [((PGreater (? number? m) (PSelf)) (? number? n))
     #f]
    [((PGreater (? number? m) (PSelf)) (PGreater (PSelf) (? number? n)))
     #f]
    [((PGreater (? number? m) (PSelf)) (PGreater (? number? n) (PSelf)))
     (<= m n)]
    [((PGreater (? number? m) (PSelf)) (PAnd _ _))
     #f]
    ;;;;;;;;;;;;;;
    [((PAnd _ _) (? number? n))
     #f]
    [((PAnd _ _) (PGreater _ _))
     #f]
    [((PAnd (PGreater (PSelf) (? number? l1)) (PGreater (? number? u1) (PSelf)))
      (PAnd (PGreater (PSelf) (? number? l2)) (PGreater (? number? u2) (PSelf))))
     (and (>= l1 l2) (>= u2 u1)
          (>= l1 u2) (>= u1 l2))]
    [else (error 'is-sub-pred? "seems that we didn't consider this situation: ~a ~a" p1 p2)]))

(define all-bools (set (BoolValue (True)) (BoolValue (False))))

; IntValue IntValue -> Set(IntValue)
(define (int/+ l r)
  (match* (l r)
    [((IntValue p1) (IntValue p2)) (set (IntValue (pred/+ p1 p2)))]
    [(_ _) (error 'int/+ "not an integer")]))

; Predicate Predicate -> Predicate
(define (pred/+ p1 p2)
  (match* (p1 p2)
    [((? number?) (? number?)) (+ p1 p2)]
    [((? number? l) (PGreater (PSelf) (? number? r)))
     (PGreater (PSelf) (+ l r))]
    [((? number? l) (PGreater (? number? r) (PSelf)))
     (PGreater (+ l r) (PSelf))]
    [((? number? l) (PAnd (PGreater (PSelf) (? number? r1))
                          (PGreater (? number? r2) (PSelf))))
     (PAnd (PGreater (PSelf) (+ l r1))
           (PGreater (+ l r2) (PSelf)))]
    ;;;;;;
    [((? PGreater? l) (? number? r))
     (pred/+ r l)]
    [((PGreater (PSelf) (? number? l-num)) (PGreater (PSelf) (? number? r-num)))
     (PGreater (PSelf) (+ l-num r-num))]
    [((PGreater (PSelf) (? number? l-num)) (PGreater (? number? r-num) (PSelf)))
     #t]
    [((PGreater (? number? l-num) (PSelf)) (PGreater (? number? r-num) (PSelf)))
     (PGreater (+ l-num r-num) (PSelf))]
    [((PGreater (? number? l-num) (PSelf)) (PGreater (PSelf) (? number? r-num)))
     (pred+ r l)]
    [((PGreater (PSelf) (? number? l-num)) (PAnd (PGreater (PSelf) (? number? r1))
                                                 (PGreater (? number? r2) (PSelf))))
     (PGreater (PSelf) (+ l-num r1))]
    [((PGreater (? number? l-num) (PSelf)) (PAnd (PGreater (PSelf) (? number? r1))
                                                 (PGreater (? number? r2) (PSelf))))
     (PGreater (+ l-num r2) (PSelf))]
    ;TODO
    [else "TODO"]))

; IntValue -> Set(IntValue)
(define (de/or i)
  ; Predicate -> [Predicate]
  (define (aux pred)
    (match pred
      [(POr p1 p2) (flatten (list (aux p1) (aux p2)))]
      [(PAnd p1 p2)
       (for/list ([pair (cartesian-product (aux p1) (aux p2))])
         (PAnd (first pair) (second pair)))]
      [(PNot p) (map PNot (aux p))]
      [p (list p)]))
  (define preds (aux (IntValue-pred i)))
  (list->set (map IntValue preds)))

; IntValue -> Set(IntValue)
(define (de/not i)
  ; Predicate -> [Predicate]
  (define (aux pred)
    (match pred
      [(PNot (? number? m))
       (list (PGreater (PSelf) m) (PGreater m (PSelf)))]
      [(PNot (PGreater (PSelf) m))
       (list m (PGreater m (PSelf)))]
      [(PNot (PGreater m (PSelf)))
       (list m (PGreater (PSelf) m))]
      [(PNot (PAnd p1 p2))
       (append (aux (PNot p1)) (aux (PNot p2)))]
      [(PAnd p1 p2)
       (for/list ([pair (cartesian-product (aux p1) (aux p2))])
         (PAnd (first pair) (second pair)))]
      [p (list p)]))
  (define preds (aux (IntValue-pred i)))
  (list->set (map IntValue preds)))

; Predicate -> Predicate
(define (reorder-pand pred)
  (match pred
    [(PAnd (? PGreater? l) (? number? r))
     (PAnd r l)]
    [(PAnd (PGreater (? number?) (PSelf)) (PGreater (PSelf) (? number?)))
     (swap/pand pred)]
    [(PAnd l r) (PAnd (reorder-pand l) (reorder-pand r))]
    [p p]))

; Predicate -> Boolean
(define (is-valid-pred? pred)
  (match pred
    [(PAnd (? number? m) (? number? n))
     (= m n)]
    [(PAnd (? number? m) (PGreater (PSelf) (? number? n)))
     (> m n)]
    [(PAnd (? number? m) (PGreater (? number? n) (PSelf)))
     (< m n)]
    [(PAnd (PGreater (PSelf) (? number? l-num)) (PGreater (? number? r-num) (PSelf)))
     (<= l-num r-num)]
    [(PAnd (PAnd (PGreater (PSelf) (? number? l1))
                 (PGreater (? number? u1) (PSelf)))
           (PAnd (PGreater (PSelf) (? number? l2))
                 (PGreater (? number? u2) (PSelf))))
     (or (and (>= l1 l2) (>= u2 u1))
         (and (>= l2 l1) (>= u1 u2))
         (and (>= u1 l2) (>= u2 l1) (>= l2 l1) (>= u2 u1))
         (and (>= u2 l1) (>= u1 l2) (>= l1 l2) (>= u1 u2)))]
    [(PAnd l r) (and (is-valid-pred? l) (is-valid-pred? r))]
    [else #t]))

; Predicate -> Predicate
(define (reduce pred)
  (match pred
    [(PAnd (? number? m) (PGreater _ _))
     m]
    [(PAnd (PGreater (PSelf) (? number? m))
           (PGreater (PSelf) (? number? n)))
     (PGreater (PSelf) (max m n))]
    [(PAnd (PGreater (? number? m) (PSelf))
           (PGreater (? number? n) (PSelf)))
     (PGreater (min m n) (PSelf))]
    [(PAnd (PAnd (PGreater (PSelf) (? number? l1))
                 (PGreater (? number? u1) (PSelf)))
           (PAnd (PGreater (PSelf) (? number? l2))
                 (PGreater (? number? u2) (PSelf))))
     (cond
       [(and (>= l1 l2) (>= u2 u1))
        (PAnd (PGreater (PSelf) l1)
              (PGreater u1 (PSelf)))]
       [(and (>= l2 l1) (>= u1 u2))
        (PAnd (PGreater (PSelf) l2)
              (PGreater u2 (PSelf)))]
       [(and (>= u1 l2) (>= u2 l1) (>= l2 l1) (>= u2 u1))
        (PAnd (PGreater (PSelf) l2)
              (PGreater u1 (PSelf)))]
       [(and (>= u2 l1) (>= u1 l2) (>= l1 l2) (>= u1 u2))
        (PAnd (PGreater (PSelf) l1)
              (PGreater u2 (PSelf)))]
       [else (error 'reduce "never should happend")])]
    [(PAnd (PGreater (PSelf) (? number?))
           (PGreater (? number?) (PSelf)))
     pred]
    [(PAnd (? PAnd? l) (? PAnd? r))
     (reduce (PAnd (reduce l) (reduce r)))]
    [p p]))

(module+ test
  (is-valid-pred? (PAnd 3 (PGreater (PSelf) 2)))
  (is-valid-pred? (PAnd 3 (PGreater 4 (PSelf))))
  (is-valid-pred? (PAnd (PAnd (PGreater (PSelf) 1)
                              (PGreater 9 (PSelf)))
                        (PAnd (PGreater (PSelf) 0)
                              (PGreater 5 (PSelf)))))
  (is-valid-pred? (PAnd (PAnd (PGreater (PSelf) 0)
                              (PGreater 5 (PSelf)))
                        (PAnd (PGreater (PSelf) 1)
                              (PGreater 9 (PSelf)))))
  (is-valid-pred? (PAnd (PGreater (PSelf) 1) (PGreater 5 (PSelf))))
  (is-valid-pred? (PAnd (PAnd 4 (PGreater (PSelf) 2))
                        (PAnd (PGreater (PSelf) 0)
                              (PGreater (PSelf) 1))))
  (is-valid-pred? (PAnd (PAnd 4 (PGreater (PSelf) 2))
                        (PAnd (PGreater (PSelf) 1)
                              (PGreater 0 (PSelf)))))
  (is-valid-pred? (PAnd (PAnd (PGreater (PSelf) 0)
                              (PGreater 5 (PSelf)))
                        (PAnd (PGreater (PSelf) 6)
                              (PGreater 9 (PSelf)))))
  (is-valid-pred? (PAnd 1 2))
  (is-valid-pred? (PAnd 1 (PGreater (PSelf) 3)))
  
  (reduce (PAnd 3 (PGreater (PSelf) 2)))
  (reduce (PAnd 3 (PGreater 4 (PSelf))))
  (reduce (PAnd (PAnd (PGreater (PSelf) 1)
                      (PGreater 9 (PSelf)))
                (PAnd (PGreater (PSelf) 0)
                      (PGreater 5 (PSelf)))))
  (reduce (PAnd (PAnd (PGreater (PSelf) 0)
                      (PGreater 5 (PSelf)))
                (PAnd (PGreater (PSelf) 1)
                      (PGreater 9 (PSelf)))))
  (reduce (PAnd (PGreater (PSelf) 1) (PGreater 5 (PSelf))))
  (reduce (PAnd (PAnd 4 (PGreater (PSelf) 2))
                (PAnd (PGreater (PSelf) 0)
                      (PGreater (PSelf) 1))))
  
  (de/not (IntValue 1))
  (de/not (IntValue (PNot 1)))
  (de/not (IntValue (PNot (PGreater (PSelf) 3))))
  (de/not (IntValue (PNot (PGreater 3 (PSelf)))))
  (de/not (IntValue (PNot (PAnd (PGreater (PSelf) 3)
                                (PGreater 5 (PSelf))))))
  (de/not (IntValue (PAnd (PNot 3) (PNot 5))))
  
  (de/or (IntValue 1))
  (de/or (IntValue (POr 1 2)))
  (de/or (IntValue (PAnd (PGreater (PSelf) 1) (PGreater 2 (PSelf)))))
  (de/or (IntValue (PNot 2)))
  (de/or (IntValue (PGreater (PSelf) 2)))
  (de/or (IntValue (PGreater 3 (PSelf))))
  (de/or (IntValue (PAnd (POr (PGreater (PSelf) 5)
                              (PGreater 0 (PSelf)))
                         (POr 1 6))))
  (de/or (IntValue (POr (PNot 3) (PNot 4))))
  (de/or (IntValue (PAnd (POr 3 (PGreater (PSelf) 5))
                         (PAnd (PGreater 10 (PSelf))
                               (PGreater (PSelf) 2))))))
   
; IntValue IntValue -> Set(IntValue)
(define (int/- l r)
  (match* (l r)
    [((IntValue p1) (IntValue p2)) (Set (IntValue #t))]
    [(_ _) (error 'int/- "not an integer")]))

; IntValue IntValue -> Set(IntValue)
(define (int/* l r)
  (match* (l r)
    [((IntValue p1) (IntValue p2)) (Set (IntValue #t))]
    [(_ _) (error 'int/* "not an integer")]))

; BoolValue BoolValue -> Set(BoolValue)
(define (bool/and l r)
  (match* (l r)
    [((BoolValue p1) (BoolValue p2)) all-bools]
    [(_ _) (error 'bool/and "not an bool")]))

; BoolValue BoolValue -> Set(BoolValue)
(define (bool/or l r)
  (match* (l r)
    [((BoolValue p1) (BoolValue p2)) all-bools]
    [(_ _) (error 'bool/and "not an bool")]))

; BoolValue -> Set(BoolValue)
(define (bool/not b)
  (match b
    [(BoolValue (True)) (set (BoolValue (False)))]
    [(BoolValue (False)) (set (BoolValue (True)))]
    [_ (error 'bool/not "not a bool")]))

; IntValue IntValue -> Set(BoolValue)
(define (int/eq l r)
  (match* (l r)
    [((IntValue (? number? l-num)) (IntValue (? number? r-num)))
     (set (if (= l-num r-num)
              (BoolValue (True))
              (BoolValue (False))))]
    [((IntValue (PGreater (PSelf) (? number? l-num)))
      (IntValue (PGreater (? number? r-num) (PSelf))))
     (if (> l-num r-num)
         (set (BoolValue (False)))
         all-bools)]
    [(_ _) all-bools]))
    
(define (swap/pand p)
  (match p [(PAnd l r) (PAnd r l)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;

#|

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

|#
