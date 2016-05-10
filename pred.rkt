#lang racket

(require rackunit)
(require "structs.rkt")

(provide int/+
         int/-
         int/*
         int/eq
         int/>
         bool/and
         bool/or
         bool/not
         all-bools
         pred-preprocess
         is-sub-type? is-sub-pred?)

; IntValue -> [IntValue]
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
  (remove-duplicates (map IntValue preds)))

; IntValue -> [IntValue]
(define (de/not i)
  ; Predicate -> Predicate
  (define (norm/pgreater p)
    (match p
      [(PGreater (PSelf) _)
       (PAnd p
             (PGreater +inf.f (PSelf)))]
      [(PGreater _ (PSelf))
       (PAnd (PGreater (PSelf) -inf.f)
             p)]
      [p p]))
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
  (remove-duplicates (map (compose IntValue norm/pgreater) preds)))

; Predicate -> Predicate
(define (reorder-pand pred)
  (match pred
    [(PAnd (PGreater (? number?) (PSelf)) (PGreater (PSelf) (? number?)))
     (swap/pand pred)]
    [(PAnd l r) (PAnd (reorder-pand l) (reorder-pand r))]
    [p p]))

; Predicate -> Boolean
(define (is-valid-pred? pred)
  (match pred
    [(PAnd (? number? m) (? number? n))
     (= m n)]
    [(PAnd (? number? m) (PGreater (PSelf) (? number? l)))
     (> m l)]
    [(PAnd (? number? m) (PGreater (? number? u) (PSelf)))
     (< m u)]
    [(PAnd (? number? m) (PAnd (PGreater (PSelf) (? number? l))
                               (PGreater (? number? u) (PSelf))))
     (and (> m l) (< m u))]
    [(PAnd p (? number? m))
     (is-valid-pred? (PAnd m p))]   
    [(or (PAnd (PGreater (PSelf) _) (PGreater (PSelf) _))
         (PAnd (PGreater _ (PSelf)) (PGreater _ (PSelf))))
     #t]
    [(PAnd (PGreater (PSelf) (? number? l)) (PGreater (? number? u) (PSelf)))
     (<= l u)]
    
    [(PAnd (PAnd (PGreater (PSelf) (? number? l1))
                 (PGreater (? number? u1) (PSelf)))
           (PAnd (PGreater (PSelf) (? number? l2))
                 (PGreater (? number? u2) (PSelf))))
     (< (max l1 l2) (min u1 u2))]
    
    [(PAnd l r) (and (is-valid-pred? l) (is-valid-pred? r))]
    [(PGreater _ _) #f]
    [else #t]))


; Predicate -> Predicate
(define (reduce pred)
  (match pred
    [(PAnd (? number? m) (? PGreater?))
     m]
    [(PAnd (? PGreater?) (? number? m))
     m]
    [(PAnd (? number? m) (PAnd (PGreater (PSelf) l)
                               (PGreater u (PSelf))))
     m]
    [(PAnd (PGreater (PSelf) (? number? m))
           (PGreater (PSelf) (? number? n)))
     (PAnd (PGreater (PSelf) (max m n))
           (PGreater +inf.f (PSelf)))]
    [(PAnd (PGreater (? number? m) (PSelf))
           (PGreater (? number? n) (PSelf)))
     (PAnd (PGreater (PSelf) -inf.f)
           (PGreater (min m n) (PSelf)))]
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
       [(and (>= u1 l2) (>= u2 l1))
        (PAnd (PGreater (PSelf) (max l1 l2))
              (PGreater (min u1 u2) (PSelf)))]
       [else (error 'reduce "never should happend")])]
    [(PAnd (PGreater (PSelf) (? number?))
           (PGreater (? number?) (PSelf)))
     pred]
    [(PAnd (? PAnd? l) (? PAnd? r))
     (reduce (PAnd (reduce l) (reduce r)))]
    [p p]))

(module+ test
  (check-true (is-valid-pred? (PAnd 3 (PAnd (PGreater (PSelf) 2)
                                            (PGreater +inf.f (PSelf))))))
  
  (check-true (is-valid-pred? (PAnd 3 (PAnd (PGreater (PSelf) -inf.f)
                                            (PGreater 4 (PSelf))))))
  (check-true (is-valid-pred? (PAnd (PAnd (PGreater (PSelf) 1)
                                          (PGreater 9 (PSelf)))
                                    (PAnd (PGreater (PSelf) 0)
                                          (PGreater 5 (PSelf))))))
  (check-true (is-valid-pred? (PAnd (PAnd (PGreater (PSelf) 0)
                                          (PGreater 5 (PSelf)))
                                    (PAnd (PGreater (PSelf) 1)
                                          (PGreater 9 (PSelf))))))
  (check-true (is-valid-pred? (PAnd (PGreater (PSelf) 1)
                                    (PGreater 5 (PSelf)))))
  (check-true (is-valid-pred? (PAnd (PAnd 4 (PGreater (PSelf) 2))
                                    (PAnd (PGreater (PSelf) 0)
                                          (PGreater (PSelf) 1)))))

  (check-false (is-valid-pred? (PAnd (PAnd 4 (PGreater (PSelf) 2))
                                     (PAnd (PGreater (PSelf) 1)
                                           (PGreater 0 (PSelf))))))
  (check-false (is-valid-pred? (PAnd (PAnd (PGreater (PSelf) 0)
                                           (PGreater 5 (PSelf)))
                                     (PAnd (PGreater (PSelf) 6)
                                           (PGreater 9 (PSelf))))))
  (check-false (is-valid-pred? (PAnd 1 2)))
  (check-false (is-valid-pred? (PAnd 1 (PGreater (PSelf) 3))))

  (check-equal? (reduce (PAnd 3 (PGreater (PSelf) 2)))
                3)
  (check-equal? (reduce (PAnd 3 (PGreater 4 (PSelf))))
                3)
 
  (check-equal? (reduce (PAnd (PAnd (PGreater (PSelf) 1)
                                    (PGreater 9 (PSelf)))
                              (PAnd (PGreater (PSelf) 0)
                                    (PGreater 5 (PSelf)))))
                (PAnd (PGreater (PSelf) 1) (PGreater 5 (PSelf))))
  (check-equal? (reduce (PAnd (PAnd (PGreater (PSelf) 0)
                                    (PGreater 5 (PSelf)))
                              (PAnd (PGreater (PSelf) 1)
                                    (PGreater 9 (PSelf)))))
                (PAnd (PGreater (PSelf) 1) (PGreater 5 (PSelf))))

  (check-equal? (reduce (PAnd (PGreater (PSelf) 1) (PGreater 5 (PSelf))))
                (PAnd (PGreater (PSelf) 1) (PGreater 5 (PSelf))))
  (check-equal? (reduce (PAnd (PAnd 4 (PGreater (PSelf) 2))
                              (PAnd (PGreater (PSelf) 0)
                                    (PGreater (PSelf) 1))))
                4)
  (check-equal? (list->set (de/not (IntValue 1)))
                (set (IntValue 1)))
  (check-equal? (list->set (de/not (IntValue (PNot 1))))
                (set (IntValue (PAnd (PGreater (PSelf) 1)
                                     (PGreater +inf.f (PSelf))))
                     (IntValue (PAnd (PGreater (PSelf) -inf.f)
                                     (PGreater 1 (PSelf))))))
  (check-equal? (list->set (de/not (IntValue (PNot (PGreater (PSelf) 3)))))
                (set (IntValue 3)
                     (IntValue (PAnd (PGreater (PSelf) -inf.f)
                                     (PGreater 3 (PSelf))))))
  (check-equal? (list->set (de/not (IntValue (PNot (PGreater 3 (PSelf))))))
                (set (IntValue (PAnd (PGreater (PSelf) 3)
                                     (PGreater +inf.f (PSelf))))
                     (IntValue 3))) 
  (check-equal? (list->set (de/not (IntValue (PNot (PAnd (PGreater (PSelf) 3)
                                                         (PGreater 5 (PSelf)))))))
                (set
                 (IntValue 5)
                 (IntValue 3)
                 (IntValue (PAnd (PGreater (PSelf) 5)
                                 (PGreater +inf.f (PSelf))))
                 (IntValue (PAnd (PGreater (PSelf) -inf.f)
                                 (PGreater 3 (PSelf))))))
  (check-equal? (list->set (de/not (IntValue (PAnd (PNot 3) (PNot 5)))))
                (set
                 (IntValue (PAnd (PGreater (PSelf) 3) (PGreater (PSelf) 5)))
                 (IntValue (PAnd (PGreater (PSelf) 3) (PGreater 5 (PSelf))))
                 (IntValue (PAnd (PGreater 3 (PSelf)) (PGreater (PSelf) 5)))
                 (IntValue (PAnd (PGreater 3 (PSelf)) (PGreater 5 (PSelf))))))

  (check-equal? (list->set (de/or (IntValue 1)))
                (set (IntValue 1)))
  (check-equal? (list->set (de/or (IntValue (POr 1 2))))
                (set (IntValue 2) (IntValue 1)))
  (check-equal? (list->set (de/or (IntValue (PAnd (PGreater (PSelf) 1) (PGreater 2 (PSelf))))))
                (set (IntValue (PAnd (PGreater (PSelf) 1) (PGreater 2 (PSelf))))))
  (check-equal? (list->set (de/or (IntValue (PNot 2))))
                (set (IntValue (PNot 2))))
  (check-equal? (list->set (de/or (IntValue (PGreater (PSelf) 2))))
                (set (IntValue (PGreater (PSelf) 2))))
  (check-equal? (list->set (de/or (IntValue (PGreater 3 (PSelf)))))
                (set (IntValue (PGreater 3 (PSelf)))))
  (check-equal? (list->set (de/or (IntValue (PAnd (POr (PGreater (PSelf) 5)
                                                       (PGreater 0 (PSelf)))
                                                  (POr 1 6)))))
                (set
                 (IntValue (PAnd (PGreater (PSelf) 5) 1))
                 (IntValue (PAnd (PGreater 0 (PSelf)) 6))
                 (IntValue (PAnd (PGreater 0 (PSelf)) 1))
                 (IntValue (PAnd (PGreater (PSelf) 5) 6))))    
  (check-equal? (list->set (de/or (IntValue (POr (PNot 3) (PNot 4)))))
                (set (IntValue (PNot 3)) (IntValue (PNot 4))))

  (check-equal? (list->set (de/or (IntValue (PAnd (POr 3 (PGreater (PSelf) 5))
                                                  (PAnd (PGreater 10 (PSelf))
                                                        (PGreater (PSelf) 2))))))
                (set
                 (IntValue (PAnd (PGreater (PSelf) 5)
                                 (PAnd (PGreater 10 (PSelf)) (PGreater (PSelf) 2))))
                 (IntValue (PAnd 3
                                 (PAnd (PGreater 10 (PSelf))
                                       (PGreater (PSelf) 2))))))
)

(define pred-preprocess
  (compose (curry map IntValue)
           (curry map (compose reduce IntValue-pred))
           (curry filter is-valid-pred?)
           (curry map reorder-pand)
           (curry apply set-union)
           (curry map de/not)
           de/or))

; TODO inline/expand
; !!!! TODO int/+ int/- int/* bool/and bool/or

(define (is-sub-type? t1 t2)
  (match* (t1 t2)
    [((IntValue _) (IntValue #t)) #t]
    [((IntValue #t) (IntValue _)) #f]
    [((IntValue p1) (IntValue p2))
     (is-sub-pred? p1 p2)]
    [((BoolValue _) (BoolValue #t)) #t]
    [((BoolValue (True)) (BoolValue (True))) #t]
    [((BoolValue (False)) (BoolValue (False))) #t]
    [(_ _) #f]))

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
    [(_ _) (error 'is-sub-pred? "seems that we didn't consider this situation: ~a ~a" p1 p2)]))
    

(define all-bools (set (BoolValue (True)) (BoolValue (False))))

; pred/+ :: Predicate Predicate -> Predicate
(define (pred/+ p1 p2)
  (match* (p1 p2)
    [(#t _) #t]
    [(_ #t) #t]
    [((? number?) (? number?)) (+ p1 p2)]
    [((? number? l) (PAnd (PGreater (PSelf) (? number? r1))
                          (PGreater (? number? r2) (PSelf))))
     (PAnd (PGreater (PSelf) (+ l r1))
           (PGreater (+ l r2) (PSelf)))]
    ;;=========
    [((PAnd (PGreater (PSelf) (? number? l1))
            (PGreater (? number? u1) (PSelf)))
      (PAnd (PGreater (PSelf) (? number? l2))
            (PGreater (? number? u2) (PSelf))))
     (PAnd (PGreater (PSelf) (+ l1 l2))
           (PGreater (+ u1 u2) (PSelf)))]
    [((? PAnd?) _) (pred/+ p2 p1)]))

; pred/- :: Predicate Predicate -> Predicate
(define (pred/- p1 p2)
  (match* (p1 p2)
    [(#t _) #t]
    [(_ #t) #t]
    [((? number?) (? number?)) (- p1 p2)]
    [((? number?) (PAnd (PGreater (PSelf) (? number? l))
                        (PGreater (? number? u) (PSelf))))
     (PAnd (PGreater (PSelf) (- p1 u))
           (PGreater (- p1 l) (PSelf)))]
    ;;=========
    [((PAnd (PGreater (PSelf) (? number? l1))
            (PGreater (? number? u1) (PSelf)))
      (PAnd (PGreater (PSelf) (? number? l2))
            (PGreater (? number? u2) (PSelf))))
     (PAnd (PGreater (PSelf) (- l1 u2))
           (PGreater (- u1 l2) (PSelf)))]    
    [((PAnd (PGreater (PSelf) (? number? l))
            (PGreater (? number? u) (PSelf)))
      (? number?))
     (PAnd (PGreater (PSelf) (- l p2))
           (PGreater (- u p2) (PSelf)))]))


(define (pred/* p1 p2)
  (match* (p1 p2)
    [(#t _) #t]
    [(_ #t) #t]
    [((? zero?) _) 0]
    [(_ (? zero?)) 0]
    [((? number?) (? number?)) (* p1 p2)]
    [((? number? num) (PAnd (PGreater (PSelf) (? number? l))
                            (PGreater (? number? u) (PSelf))))
     (let* ([candidates (list (* num l) (* num u))]
            [upper (max candidates)]
            [lower (min candidates)])
       (PAnd (PGreater (PSelf) lower)
             (PGreater upper (PSelf))))]
    ;;=========
    [((PAnd (PGreater (PSelf) (? number? l1))
            (PGreater (? number? u1) (PSelf)))
      (PAnd (PGreater (PSelf) (? number? l2))
            (PGreater (? number? u2) (PSelf))))
     (let* ([candidates (list (* l1 l2) (* l1 u2) (* u1 l2) (* u1 u2))]
            [upper (max candidates)]
            [lower (min candidates)])
       (PAnd (PGreater (PSelf) lower)
             (PGreater upper (PSelf))))]
    [((? PAnd?) _) (pred/* p2 p1)]))


; IntValue IntValue -> Set(IntValue)
(define (int/+ l r)
  (match* (l r)
    [((IntValue p1) (IntValue p2)) (set (IntValue (pred/+ p1 p2)))]
    [(_ _) (error 'int/+ "not an integer")]))

; IntValue IntValue -> Set(IntValue)
(define (int/- l r)
  (match* (l r)
    [((IntValue p1) (IntValue p2)) (set (IntValue (pred/- p1 p2)))]
    [(_ _) (error 'int/- "not an integer")]))

; IntValue IntValue -> Set(IntValue)
(define (int/* l r)
  (match* (l r)
    [((IntValue p1) (IntValue p2)) (set (IntValue (pred/* p1 p2)))]
    [(_ _) (error 'int/* "not an integer")]))

; BoolValue BoolValue -> Set(BoolValue)
(define (bool/and l r)
  (match* (l r)
    [((BoolValue (True)) (BoolValue (True))) (set (BoolValue (True)))]
    [((BoolValue (False)) (BoolValue _)) (set (BoolValue (False)))]
    [((BoolValue _) (BoolValue (False))) (set (BoolValue (False)))]
    ;[((BoolValue p1) (BoolValue p2)) all-bools]
    [(_ _) (error 'bool/and "not an bool")]))

; BoolValue BoolValue -> Set(BoolValue)
(define (bool/or l r)
  (match* (l r)
    [((BoolValue (False)) (BoolValue (False))) (set (BoolValue (False)))]
    [((BoolValue (True)) (BoolValue _)) (set (BoolValue (True)))]
    [((BoolValue _) (BoolValue (True))) (set (BoolValue (True)))]
    ;[((BoolValue p1) (BoolValue p2)) all-bools]
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
    [(#t _) all-bools]
    [(_ #t) all-bools]
    [((IntValue (? number? l-num)) (IntValue (? number? r-num)))
     (set (if (= l-num r-num)
              (BoolValue (True))
              (BoolValue (False))))]
    [((IntValue (? number? num))
      (IntValue (PAnd (PGreater (PSelf) (? number? l))
                      (PGreater (? number? u) (PSelf)))))
     (if (or (>= num u) (<= num l))
         (Set (BoolValue (False)))
         all-bools)]
    [((IntValue (PAnd (PGreater (PSelf) (? number? l1))
                      (PGreater (? number? u1) (PSelf))))
      (IntValue (PAnd (PGreater (PSelf) (? number? l2))
                      (PGreater (? number? u2) (PSelf)))))
     (if (or (and (>= l2 l1) (<= l2 u1))
             (and (>= l1 l2) (<= l1 u2)))
         all-bools
         (set (BoolValue (False))))]

    [((IntValue (PAnd (PGreater (PSelf) (? number?))
                      (PGreater (? number?) (PSelf))))
      _)
     (int/eq r l)]
    [(_ _) all-bools]))


; IntValue IntValue -> Set(BoolValue)
(define (int/> v1 v2)
  (match* (v1 v2)
    [(#t _) all-bools]
    [(_ #t) all-bools]
    [((IntValue (? number? ln)) (IntValue (? number? rn)))
     (set (if (> ln rn)
              (BoolValue (True))
              (BoolValue (False))))]
    [((IntValue (? number? num))
      (IntValue (PAnd (PGreater (PSelf) (? number? l))
                      (PGreater (? number? u) (PSelf)))))
     (cond [(>= num u) (set (BoolValue (True)))]
           [(<= num l) (set (BoolValue (True)))]
           [else all-bools])]
    [((IntValue (PAnd (PGreater (PSelf) (? number? l1))
                      (PGreater (? number? u1) (PSelf))))
      (IntValue (PAnd (PGreater (PSelf) (? number? l2))
                      (PGreater (? number? u2) (PSelf)))))
     (if (> l1 u2)
         (set (BoolValue (True)))
         all-bools)]))


(define (swap/pand p)
  (match p [(PAnd l r) (PAnd r l)]))