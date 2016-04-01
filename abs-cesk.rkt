#lang racket

(require rackunit)

(struct State (exp env store kont time) #:transparent)

; Exp
(struct Var (name) #:transparent)
(struct Lam (label var exp) #:transparent)
(struct App (fun arg) #:transparent)
(struct Int () #:transparent)
(struct Bool () #:transparent)
(struct Plus (lhs rhs) #:transparent)
(struct And (lhs rhs) #:transparent)
(struct Or (lhs rhs) #:transparent)
(struct Not (bl) #:transparent)

; Continuation
(struct DoneK () #:transparent)
(struct ArgK (exp env addr) #:transparent)
(struct AppK (lam env addr) #:transparent)
(struct PlusK (r env store addr) #:transparent)
(struct DoPlusK (l addr) #:transparent)
(struct AndK (r env store addr) #:transparent)
(struct DoAndK (l addr) #:transparent)
#|
TODO
(struct OrK (...) #:transparent)
(struct DoOrK (...) #:transparent)
(struct DoNotK (...) #:transparent)
|#

; Storable
(struct Clo (lam env))
(struct Cont (k))
(struct IntValue ())
(struct BoolValue ())

; Env : var -> addr

; lookup-env env var
(define lookup-env hash-ref)
; ext-env env var addr
(define ext-env hash-set)
(define mt-env (make-immutable-hasheq))

; Store : addr -> Set(value)

; lookup-store : store addr -> Set(value)
(define (lookup-store store addr)
  (if (hash-has-key? store addr)
      (hash-ref store addr)
      (set)))
; ext-store : store addr val -> store
(define (ext-store store addr val)
  (if (hash-has-key? store addr)
      (let ([old-vals (lookup-store store addr)])
        (hash-set store addr (set-union old-vals (set val))))
      (hash-set store addr (set val))))
(define mt-store (make-immutable-hasheq))

(define (alloc s)
  (+ 1 (foldl max 0 (hash-keys (State-store s)))))

(define (tick s)
  (+ 1 (State-time s)))

; step : state -> [state]
(define (step s)
  (match s
    [(State (Int) env store k t)
     (list (State (IntValue) env store k (tick s)))]
    [(State (Bool) env store k t)
     (list (State (BoolValue) env store k (tick s)))]
    [(State (Var x) env store k t)
     (for/list ([val (set->list (lookup-store store (lookup-env env x)))])
       (cond [(Clo? val) (State (Clo-lam val) (Clo-env val) store k (tick s))]
             [else (State val env store k (tick s))]))]
    [(State (App fun arg) env store k t)
     (define addr (alloc s))
     (define new-store (ext-store store addr (Cont k)))
     (define new-k (ArgK arg env addr))
     (list (State fun env new-store new-k (tick s)))]
    [(State (Lam label var exp) env store (ArgK e k-env k-addr) t) ;TODO (Lam var exp)
     (list (State e k-env store (AppK (Lam label var exp) env k-addr) (tick s)))]
    [(State exp env store (AppK (Lam label x e) k-env k-addr) t)
     (define val
       (cond [(Lam? exp) (Clo exp env)]
             [else exp]))
     (define v-addr (alloc s))
     (for/list ([k (set->list (lookup-store store k-addr))])
       (State e (ext-env k-env x v-addr) (ext-store store v-addr val) (Cont-k k) (tick s)))]
    [(State (Plus l r) env store k t)
     (define k-addr (alloc s))
     (define new-store (ext-store store k-addr (Cont k)))
     (define new-k (PlusK r env new-store k-addr))
     (list (State l env new-store new-k (tick s)))]
    [(State l env store (PlusK r r-env r-store k-addr) t)
     (list (State r r-env r-store (DoPlusK l k-addr) (tick s)))]
    [(State r env store (DoPlusK l k-addr) t)
     (check-true (IntValue? l))
     (check-true (IntValue? r))
     (for/list ([k (set->list (lookup-store store k-addr))])
        (State (IntValue) env store (Cont-k k) (tick s)))]
    [(State (And l r) env store k t)
     ;TODO
     (define k-addr (alloc s))
     (define new-store (ext-store store k-addr (Cont k)))
     (define new-k (AndK r env new-store k-addr))
     (list (State l env new-store new-k (tick s)))]
    [(State l env store (AndK r r-env r-store k-addr) t)
     (list (State r r-env r-store (DoAndK l k-addr) (tick s)))]
    [(State r env store (DoAndK l k-addr) t)
     (check-true (BoolValue? l))
     (check-true (BoolValue? r))
     (for/list ([k (set->list (lookup-store store k-addr))])
        (State (BoolValue) env store (Cont-k k) (tick s)))]
    [s (list s)]))

(define (inject e)
  (State e mt-env mt-store (DoneK) 0))

(define (explore f s)
  (search f (set) (list s)))

(define (search f seen todo)
  (cond [(empty? todo) seen]
        [(set-member? seen (first todo))
         (search f seen (cdr todo))]
        [else (search f (set-add seen (first todo))
                      (append (f (first todo)) (cdr todo)))]))

(define (sort-state-set states)
  (sort (set->list states) < #:key State-time))

; exp -> [state]
(define (aval e)
  (sort-state-set (explore step (inject e))))

(module+ test
  (check-equal? (ext-store mt-store 1 'a)
                (hasheq 1 (set 'a)))
  (check-equal? (ext-store (ext-store mt-store 1 'a) 1 'b)
                (hasheq 1 (set 'a 'b)))
  (check-equal? (ext-store (ext-store (ext-store mt-store 1 'a) 1 'b) 2 'c)
                (hasheq 1 (set 'a 'b) 2 (set 'c))))

(define (parse exp)
  (match exp
    ['true (Bool)]
    ['false (Bool)]
    [(? integer?) (Int)]
    [(? symbol?) (Var exp)]
    [`(+ ,lhs ,rhs)
     (Plus (parse lhs) (parse rhs))]
    [`(and ,lhs ,rhs)
     (And (parse lhs) (parse rhs))]
    [`(or ,lhs ,rhs)
     (Or (parse lhs) (parse rhs))]
    [`(not ,bl)
     (Not (parse bl))]
    [`(lambda ,label (,var) ,body) (Lam label var (parse body))]
    [`(lambda (,var) ,body) (Lam (gensym 'λ) var (parse body))]
    [`(,rator ,rand) (App (parse rator) (parse rand))]))
    
;(aval (App (Lam "x" (Var "x")) (Lam "y" (Var "y"))))
;(aval (Lam "x" (Var "x")))

(aval (parse '{{lambda {x} x} {lambda {y} y}}))
;(aval (parse '{{lambda fz {z} z} {{lambda fx {x} x} {lambda fy {y} y}}}))
;(aval (parse '{lambda {x} x}))
(aval (parse '{lambda {x} x}))
(aval (parse 3))
;(aval (parse 'true))
;(aval (parse 'false))

(aval (parse '{+ 1 2}))
(aval (parse '{and true false}))
(aval (parse '{{lambda {x} x} 1}))
