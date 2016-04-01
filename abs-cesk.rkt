#lang racket

;TODO
; Integer, +, Continuation
; Bool, and, Continuation

(require rackunit)

(struct State (exp env store kont time) #:transparent)

; Exp
(struct Var (name) #:transparent)
(struct Lam (label var exp) #:transparent)
(struct App (fun arg) #:transparent)

; Continuation
(struct DoneK () #:transparent)
(struct ArgK (exp env addr) #:transparent)
(struct AppK (lam env addr) #:transparent)

; Storable
(struct Clo (lam env))
(struct Cont (k))

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
    [(State (Var x) env store k t)
     (for/list ([val (set->list (lookup-store store (lookup-env env x)))])
       (State (Clo-lam val) (Clo-env val) store k (tick s)))]
    [(State (App fun arg) env store k t)
     (define addr (alloc s))
     (define new-store (ext-store store addr (Cont k)))
     (define new-k (ArgK arg env addr))
     (list (State fun env new-store new-k (tick s)))]
    [(State (Lam label var exp) env store (ArgK e k-env k-addr) t)
     (list (State e k-env store (AppK (Lam label var exp) env k-addr) (tick s)))]
    [(State (Lam arg-label var exp) env store (AppK (Lam fun-lab x e) k-env k-addr) t)
     ; x -> (Lam arg-label var exp)
     (define v-addr (alloc s))
     (for/list ([k (set->list (lookup-store store k-addr))])
       (State e (ext-env k-env x v-addr)
              (ext-store store v-addr (Clo (Lam arg-label var exp) env)) (Cont-k k) (tick s)))]
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
    [(? symbol?) (Var exp)]
    [`(lambda ,label (,var) ,body) (Lam label var (parse body))]
    [`(lambda (,var) ,body) (Lam (gensym 'λ) var (parse body))]
    [`(,rator ,rand) (App (parse rator) (parse rand))]))
    
;(aval (App (Lam "x" (Var "x")) (Lam "y" (Var "y"))))
;(aval (Lam "x" (Var "x")))

(aval (parse '{{lambda {x} x} {lambda {y} y}}))
;(aval (parse '{{lambda fz {z} z} {{lambda fx {x} x} {lambda fy {y} y}}}))
;(aval (parse '{lambda {x} x}))