#lang racket

; TODO regard all non-false values as true
; TODO callcc
; TODO add test cases

(require rackunit)
(require "pred.rkt")
(require "parsers.rkt")
(require "structs.rkt")

(provide aval
         aval-infer
         call2type)

; Currently using 1-CFA
(define k (make-parameter 0))

; A callsite is consiste of the label of function
; and the continuation where the function returns to.
(struct Callsite (label k) #:transparent)

(define (tick s)
  (take (cons (State-exp s) (State-time s)) (k)))

(define (atomic-value? v)
  (match v
    [(? IntValue?) #t]
    [(? BoolValue?) #t]
    [(? VoidValue?) #t]
    [_ #f]))

(define (valid-value? v)
  (match v
    [(? atomic-value?) #t]
    [(? Lam?) #t]
    [_ #f]))

; Env : var -> addr
; lookup-env env var
(define lookup-env hash-ref)
; ext-env env var addr
(define ext-env hash-set)
(define mt-env (make-immutable-hash))

; Store : addr -> Set(value)
(define d-bot (set))

; lookup-store : store addr -> Set(value)
(define (lookup-store store addr)
  (hash-ref store addr d-bot))

; store-update : store adddr Set(val) -> store
(define (store-update store addr vals)
  (hash-update store addr
               (λ (d) (set-union d vals))
               d-bot))

; ext-store : store addr val -> store
(define (ext-store store addr val)
  (store-update store addr (set val)))

; store-join : store store -> store
(define (store-join s1 s2)
  (for/fold ([new-store s1])
            ([(k v) (in-hash s2)])
    (store-update new-store k v)))

(define mt-store (make-immutable-hash))

(define cont2label (make-hash))
(define call2type (make-hash))

; step : state -> [state]
(define (step s)
  (define time* (tick s))
  (define nexts
    (match s
      ; Int
      [(State (Int pred) env store k t)
       (list (State (IntValue pred) env store k time*))]
      ; Bool
      [(State (Bool pred) env store k t)
       (list (State (BoolValue pred) env store k time*))]
      ; Void
      [(State (Void) env store k t)
       (list (State (VoidValue) env store k time*))]
      ; Ref
      [(State (Var x) env store k t)
       (for/list ([val (set->list (lookup-store store (lookup-env env x)))])
         (cond [(Clo? val) (State (Clo-lam val) (Clo-env val) store k time*)]
               [else (State val env store k time*)]))]
      ; Application
      [(State (App fun arg) env store k t)
       (define k-addr (KAddr (App fun arg) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (ArgK arg env k-addr))
       (list (State fun env new-store new-k time*))]
      ; Application: evaluate argument
      [(State (Lam label var exp) env store (ArgK e k-env k-addr) t)
       (list (State e k-env store (AppK (Lam label var exp) env k-addr) time*))]
      ; Application: evaluate callee and into the body of function
      [(State (? valid-value? exp) env store (AppK (Lam label x e) k-env k-addr) t)
       (define v-addr (BAddr x t))
       (define val (if (Lam? exp) (Clo exp env) exp))
       (define new-env (ext-env k-env x v-addr))
       (define new-store (ext-store store v-addr val))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State e new-env new-store (Cont-k k) time*))]
      ; Plus
      [(State (Plus l r) env store k t)
       (define k-addr (KAddr (Plus l r) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (PlusK r env k-addr))
       (list (State l env new-store new-k time*))]
      ; Plus: after evaluate left hand side
      [(State (? valid-value? l) env store (PlusK r r-env k-addr) t)
       (check-true (IntValue? l))
       (list (State r r-env store (DoPlusK l k-addr) time*))]
      ; Plus: after evaluate right hand side
      [(State (? valid-value? r) env store (DoPlusK l k-addr) t)
       (check-true (IntValue? r))
       (define result (int/+ l r))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State result env store (Cont-k k) time*))]
      ; Minus
      [(State (Minus l r) env store k t)
       (define k-addr (KAddr (Minus l r) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (MinusK r env k-addr))
       (list (State l env new-store new-k time*))]
      ; Minus: after evaluate left hand side
      [(State (? valid-value? l) env store (MinusK r r-env k-addr) t)
       (check-true (IntValue? l))
       (list (State r r-env store (DoMinusK l k-addr) time*))]
      ; Minus: after evaluate right hand side
      [(State (? valid-value? r) env store (DoMinusK l k-addr) t)
       (check-true (IntValue? r))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (IntValue #t) env store (Cont-k k) time*))]
      ; Mult
      [(State (Mult l r) env store k t)
       (define k-addr (KAddr (Mult l r) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (MultK r env k-addr))
       (list (State l env new-store new-k time*))]
      ; Mult: after evaluate left hand side
      [(State (? valid-value? l) env store (MultK r r-env k-addr) t)
       (check-true (IntValue? l))
       (list (State r r-env store (DoMultK l k-addr) time*))]
      ; Mult: after evaluate right hand side
      [(State (? valid-value? r) env store (DoMultK l k-addr) t)
       (check-true (IntValue? r))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (IntValue #t) env store (Cont-k k) time*))]
      ; NumEq
      [(State (NumEq l r) env store k t)
       (define k-addr (KAddr (NumEq l r) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (NumEqK r env k-addr))
       (list (State l env new-store new-k time*))]
      ; NumEq: after evaluate left hand side
      [(State (? valid-value? l) env store (NumEqK r r-env k-addr) t)
       (check-true (IntValue? l))
       (list (State r r-env store (DoNumEqK l k-addr) time*))]
      ; NumEq: after evaluate right hand side
      [(State (? valid-value? r) env store (DoNumEqK l k-addr) t)
       (check-true (IntValue? r))
       (define result (int/eq l r))
       (flatten (for/list ([k (set->list (lookup-store store k-addr))])
                  (for/list ([b (set->list result)])
                    (State b env store (Cont-k k) time*))))]
      ; Logic and
      ; TODO logic operation actually allows non-boolean values
      [(State (And l r) env store k t)
       (define k-addr (KAddr (And l r) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (AndK r env k-addr))
       (list (State l env new-store new-k time*))]
      ; Logic and: after evaluate left hand side
      [(State (? valid-value? l) env store (AndK r r-env k-addr) t)
       (check-true (BoolValue? l))
       (cons (State r r-env store (DoAndK l k-addr) time*)
             (for/list ([k (set->list (lookup-store store k-addr))])
               (State (BoolValue #t) env store (Cont-k k) time*)))]
      ; Logic and: after evaluate right hand side
      [(State (? valid-value? r) env store (DoAndK l k-addr) t)
       (check-true (BoolValue? r))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (BoolValue #t) env store (Cont-k k) time*))]
      ; Logic or
      [(State (Or l r) env store k t)
       (define k-addr (KAddr (Or l r) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (OrK r env k-addr))
       (list (State l env new-store new-k time*))]
      ; Logic or: after evaluate left hand side
      [(State (? valid-value? l) env store (OrK r r-env k-addr) t)
       (check-true (BoolValue? l))
       (cons (State r r-env store (DoOrK l k-addr) time*)
             (for/list ([k (set->list (lookup-store store k-addr))])
               (State (BoolValue #t) env store (Cont-k k) time*)))]
      ; Logic or: after evaluate right hand side
      [(State (? valid-value? r) env store (DoOrK l k-addr) t)
       (check-true (BoolValue? r))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (BoolValue #t) env store (Cont-k k) time*))]
      ; Logic not
      [(State (Not b) env store k t)
       (define k-addr (KAddr (Not b) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (DoNotK k-addr))
       (list (State b env new-store new-k time*))]
      ; Logic not: after evaluate the expr
      [(State (? valid-value? b) env store (DoNotK k-addr) t)
       (check-true (BoolValue? b))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (BoolValue #t) env store (Cont-k k) time*))]
      ; If
      [(State (If tst thn els) env store k t)
       (define k-addr (KAddr (If tst thn els) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (DoIfK thn els env k-addr))
       (list (State tst env new-store new-k time*))]
      ; If: after evaluate the condition
      [(State (? valid-value? tst) env store (DoIfK thn els k-env k-addr) t)
       (check-true (BoolValue? tst))
       (define ks (set->list (lookup-store store k-addr)))
       (match (BoolValue-pred tst)
         [(True) (for/list ([k ks]) (State thn k-env store (Cont-k k) time*))]
         [(False) (for/list ([k ks]) (State els k-env store (Cont-k k) time*))]
         [#t (append (for/list ([k ks]) (State thn k-env store (Cont-k k) time*))
                     (for/list ([k ks]) (State els k-env store (Cont-k k) time*)))]
         [_ (error 'state "(BoolValue #f)!")])]
      ; Set!
      [(State (Set var val) env store k t)
       (define k-addr (KAddr (Set var val) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (SetK var k-addr))
       (list (State val env new-store (SetK var k-addr) time*))]
      ; SetK
      [(State (? valid-value? val) env store (SetK var k-addr) t)
       ; TODO Just set the store? or need to join the range set? need to reconsider.
       (define new-store (hash-set store (lookup-env env var) (set val)))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (VoidValue) env new-store (Cont-k k) time*))]
      ; Begin
      [(State (Begin s1 s2) env store k t)
       (define k-addr (KAddr (Begin s1 s2) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (BeginK s2 k-addr))
       (list (State s1 env new-store new-k time*))]
      ; BeginK: after evaluate the first expression
      [(State (? valid-value? s1) env store (BeginK s2 k-addr) t)
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State s2 env store (Cont-k k) time*))]
      ; Anything else
      [s (list s)]))

  ; If we see an AppK continuation, then it will go into the function body
  ; so we save argument type info and where it will return to.
  (match s
    [(State (? valid-value? exp) env store (AppK (Lam label x e) k-env k-addr) t)
     ;(hash-set! cont2label k-addr label)
     ;(unless (hash-has-key? call2type (Callsite label k-addr))
     ;̄    (hash-set! call2type (Callsite label k-addr) (TArrow exp (set))))
     
     (for/list ([k (set->list (lookup-store store k-addr))])
       ;TODO
       #|
       (when (hash-has-key? cont2label (Cont-k k))
         (printf "Warning: ~a already has label `~a`, wont set to `~a`\n"
                 (Cont-k k)
                 (hash-ref cont2label (Cont-k k))
                 label))
       |#
       
       ;(unless (hash-has-key? cont2label (Cont-k k))
       (hash-set! cont2label (Cont-k k) label)

       #|
       (when (hash-has-key? call2type (Callsite label (Cont-k k)))
         (printf "Warning: ~a already has type ~a, wont set to ~a\n"
                 label ;(Callsite label (Cont-k k))
                 (hash-ref call2type (Callsite label (Cont-k k)))
                 (TArrow exp (set))))
       |#
       (unless (hash-has-key? call2type (Callsite label (Cont-k k)))
         (hash-set! call2type (Callsite label (Cont-k k)) (TArrow exp (set)))))]
    [_ (void)])

  ; If the current continuation we have saved in the cont2label, which means
  ; now it finished eval the body of a function and will return to that continuation,
  ; then we put the (State-exp s) as the return type of function and save to hash table.
  (when (and (hash-has-key? cont2label (State-kont s))
             (valid-value? (State-exp s)))
    (let* ([label (hash-ref cont2label (State-kont s))]
           [cur-type (hash-ref call2type (Callsite label (State-kont s)))])
      (hash-set! call2type
                 (Callsite label (State-kont s))
                 (TArrow (TArrow-arg cur-type)
                         (set-union (set (State-exp s)) (TArrow-ret cur-type))))))

  ; return next states
  nexts)

(define (inject e)
  (State e mt-env mt-store (DoneK) '()))

(define (explore f init)
  (search f (set) (list init) 0 (list)))

(define (search f seen todo id result)
  (displayln id)
  (cond [(empty? todo) result]
        [(set-member? seen (first todo))
         (search f seen (cdr todo) id result)]
        [else (search f (set-add seen (first todo))
                      (append (f (first todo)) (cdr todo))
                      (add1 id)
                      (cons (cons id (first todo)) result))]))

; exp -> [State]
(define (aval e) (explore step (inject e)))

(define (find-lambda-type label call2type)
  (map cdr (filter (λ (item) (symbol=? (Callsite-label (car item)) label)) (hash->list call2type))))

(define (primitive->string t call2type)
  (match t
    [(BoolValue pred) "bool"]
    [(IntValue pred) "int"]
    [(VoidValue) "void"]
    [(Lam label arg body)
     (let ([lambda-types (find-lambda-type label call2type)])
       (if (null? lambda-types) (string-append "lambda " (symbol->string label))
           ; TODO: may has multiple instance with different cont in call2type hashtable
           ; now only take the first one.
           (arrow-type->string (first lambda-types) call2type)))]
    [_ (error 'primitve->string "not primitive type")]))

(define (arrow-type->string t call2type)
  (match t
    [(TArrow arg ret)
     (string-append (primitive->string arg call2type)
                    " -> "
                    (if (= 1 (set-count ret))
                        (primitive->string (set-first ret) call2type)
                        (string-append "(" (string-join (set-map ret (λ (t) (primitive->string t call2type)))) ")")))]))

; TODO: can be remove
(define (sort-state-set states)
  (sort (set->list states) < #:key State-time))

(define (aval-infer e)
  (hash-clear! cont2label)
  (hash-clear! call2type)
  (explore step (inject e))
  (extract-func-type cont2label call2type))

(define (extract-func-type cont2label call2type)
  (hash-for-each
   call2type
   (λ (key type)
     ;;;;;;
     ;(printf "func: ~a \ncont: ~a \ntype: ~a\n" (Callsite-label key) (Callsite-k key) type)
     ;(when (string-prefix? (symbol->string (Callsite-label key)) "let") (printf "\n"))
     ;;;;;;
     (let ([label (Callsite-label key)])
       (unless (string-prefix? (symbol->string label) "let")
         (printf "~a has type: ~a\n" label (arrow-type->string type call2type)))))))

(module+ test
  (check-equal? (ext-store mt-store 1 'a)
                (hash 1 (set 'a)))
  (check-equal? (ext-store (ext-store mt-store 1 'a) 1 'b)
                (hash 1 (set 'a 'b)))
  (check-equal? (ext-store (ext-store (ext-store mt-store 1 'a) 1 'b) 2 'c)
                (hash 1 (set 'a 'b) 2 (set 'c))))

;(aval-infer (parse '{{lambda add1 {x} {+ x 1}} 2}))

#;
(aval (parse '{let {{add1 {lambda add1 {x} {+ x 1}}}}
                     {add1 2}}))
call2type
