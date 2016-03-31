#lang racket

(struct State (exp env store kont time))
(struct Var (name))
(struct Lam (var exp))
(struct App (fun arg))

(struct DoneK ())
(struct ArgK (exp env addr))
(struct AppK (lam env addr))

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
(define lookup-store hash-ref)
; ext-store : store addr set(val) -> store
(define (ext-store store addr val)
  (if (hash-has-key? store addr)
      (let ([old-vals (hash-ref store addr)])
        (hash-set store addr (set-union old-vals val)))
      (hash-set store addr val)))
(define mt-store (make-immutable-hasheq))

(define (alloc s)
  (+ 1 (foldl max 0 (hash-keys (State-store s)))))

(define (tick s)
  (+ 1 (State-time s)))

; step : state -> state*
(define (step s)
  (match s
    [(State (Var x) env store k t)
     (define t^ (tick s))
     (for/list ([val (set->list (lookup-store store (lookup-env env x)))])
       (State (Clo-lam val) (Clo-env val) store k t^))]
    [(State (App fun arg) env store k t)
     (define addr (alloc s))
     (define new-store (ext-store store addr (set (Cont k))))
     (define new-k (ArgK arg env addr))
     (define t^ (tick s))
     (list (State fun env new-store new-k t^))]
    [(State (Lam var exp) env store (ArgK e k-env k-addr) t)
     (define t^ (tick s))
     (list (State e k-env store (AppK (Lam var exp) env k-addr) t^))]
    [(State (Lam var exp) env store (AppK (Lam x e) k-env k-addr) t)
     (define t^ (tick s))
     (define v-addr (alloc s))
     (for/list ([k (set->list (lookup-store store k-addr))])
       (State e (ext-env k-env x v-addr)
              (ext-store store v-addr (Clo (Lam var exp) env)) k t^))]
    [s s]))

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

(define (aval e)
  (explore step (inject e)))

(aval (App (Lam "x" (Var "x")) (Lam "y" (Var "y"))))
