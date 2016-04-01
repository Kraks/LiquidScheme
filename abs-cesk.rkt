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
;;
(struct If (tst thn els) #:transparent)
;;

; Continuation
(struct DoneK () #:transparent)
(struct ArgK (exp env addr) #:transparent)
(struct AppK (lam env addr) #:transparent)
(struct PlusK (r env store addr) #:transparent)
(struct DoPlusK (l addr) #:transparent)
(struct AndK (r env store addr) #:transparent)
(struct DoAndK (l addr) #:transparent)
(struct OrK (r env store addr) #:transparent)
(struct DoOrK (l addr) #:transparent)
(struct DoNotK (addr) #:transparent)
(struct DoIfK (thn els addr) #:transparent)

; Storable
(struct Clo (lam env) #:transparent)
(struct Cont (k) #:transparent)
(struct IntValue () #:transparent)
(struct BoolValue () #:transparent)

(struct Callsite (label k) #:transparent)
(struct ArrowType (arg ret) #:transparent)

(define (isPrimitive? v)
  (match v
    [(? Lam?) #t]
    [(? Clo?) #t]
    [(? IntValue?) #t]
    [(? BoolValue?) #t]
    [_ #f]))

; Env : var -> addr

; lookup-env env var
(define lookup-env hash-ref)
; ext-env env var addr
(define ext-env hash-set)
(define mt-env (make-immutable-hash))

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
(define mt-store (make-immutable-hash))

(define (alloc s)
  (+ 1 (foldl max 0 (hash-keys (State-store s)))))

(define (tick s)
  (+ 1 (State-time s)))

; Callsite -> list
(define call2type (make-hash))
; Cont -> label
(define k2call (make-hash))

; step : state -> [state]
(define (step s)
  (if (and (hash-has-key? k2call (State-kont s))
           (isPrimitive? (State-exp s)))
      (let* ([label (hash-ref k2call (State-kont s))]
             [cur-type (hash-ref call2type (Callsite label (State-kont s)))])
        (hash-set! call2type (Callsite label (State-kont s))
                   (ArrowType (ArrowType-arg cur-type)
                              (set-union (ArrowType-ret cur-type) (set (State-exp s))))))
        (void))
  (match s
    ; Int
    [(State (Int) env store k t)
     (list (State (IntValue) env store k (tick s)))]
    ; Bool
    [(State (Bool) env store k t)
     (list (State (BoolValue) env store k (tick s)))]
    ; Ref
    [(State (Var x) env store k t)
     (for/list ([val (set->list (lookup-store store (lookup-env env x)))])
       (cond [(Clo? val) (State (Clo-lam val) (Clo-env val) store k (tick s))]
             [else (State val env store k (tick s))]))]
    ; Application
    [(State (App fun arg) env store k t)
     (define k-addr (alloc s))
     (define new-store (ext-store store k-addr (Cont k)))
     (define new-k (ArgK arg env k-addr))
     (list (State fun env new-store new-k (tick s)))]
    ; Application: evaluate argument
    [(State (Lam label var exp) env store (ArgK e k-env k-addr) t)
     (list (State e k-env store (AppK (Lam label var exp) env k-addr) (tick s)))]
    ; Application: evaluate callee and into the body of function
    [(State exp env store (AppK (Lam label x e) k-env k-addr) t)
     (define val
       (cond [(Lam? exp) (Clo exp env)]
             [else exp]))
     (define v-addr (alloc s))
     (for/list ([k (set->list (lookup-store store k-addr))])
       ; save argument type info and callsite info
       (hash-set! k2call (Cont-k k) label)
       (hash-set! call2type (Callsite label (Cont-k k)) (ArrowType exp (set)))
       (State e (ext-env k-env x v-addr) (ext-store store v-addr val) (Cont-k k) (tick s)))]
    ; Plus
    [(State (Plus l r) env store k t)
     (define k-addr (alloc s))
     (define new-store (ext-store store k-addr (Cont k)))
     (define new-k (PlusK r env new-store k-addr))
     (list (State l env new-store new-k (tick s)))]
    ; Plus: evaluate left hand side
    [(State l env store (PlusK r r-env r-store k-addr) t)
     (list (State r r-env r-store (DoPlusK l k-addr) (tick s)))]
    ; Plus: evaluate right hand side
    [(State r env store (DoPlusK l k-addr) t)
     (check-true (IntValue? l))
     (check-true (IntValue? r))
     (for/list ([k (set->list (lookup-store store k-addr))])
        (State (IntValue) env store (Cont-k k) (tick s)))]
    ; Logic and
    [(State (And l r) env store k t)
     (define k-addr (alloc s))
     (define new-store (ext-store store k-addr (Cont k)))
     (define new-k (AndK r env new-store k-addr))
     (list (State l env new-store new-k (tick s)))]
    ; Logic and: evaluate left hand side
    [(State l env store (AndK r r-env r-store k-addr) t)
     (check-true (BoolValue? l))
     (cons (State r r-env r-store (DoAndK l k-addr) (tick s))
           (for/list ([k (set->list (lookup-store store k-addr))])
             (State (BoolValue) env store (Cont-k k) (tick s))))]
    ; Logic and: evaluate right hand side
    [(State r env store (DoAndK l k-addr) t)
     (check-true (BoolValue? r))
     (for/list ([k (set->list (lookup-store store k-addr))])
        (State (BoolValue) env store (Cont-k k) (tick s)))]
    ; Logic or
    [(State (Or l r) env store k t)
     (define k-addr (alloc s))
     (define new-store (ext-store store k-addr (Cont k)))
     (define new-k (OrK r env new-store k-addr))
     (list (State l env new-store new-k (tick s)))]
    ; Logic or: evaluate left hand side
    [(State l env store (OrK r r-env r-store k-addr) t)
     (check-true (BoolValue? l))
     (cons (State r r-env r-store (DoOrK l k-addr) (tick s))
           (for/list ([k (set->list (lookup-store store k-addr))])
             (State (BoolValue) env store (Cont-k k) (tick s))))]
    ; Logic or: evaluate right hand side
    [(State r env store (DoOrK l k-addr) t)
     (check-true (BoolValue? r))
     (for/list ([k (set->list (lookup-store store k-addr))])
       (State (BoolValue) env store (Cont-k k) (tick s)))]
    ; Logic not
    [(State (Not bl) env store k t)
     (define k-addr (alloc s))
     (define new-store (ext-store store k-addr (Cont k)))
     (define new-k (DoNotK k-addr))
     (list (State bl env new-store new-k (tick s)))]
    ; Logic not: evaluate the expr
    [(State bl env store (DoNotK k-addr) t)
     (check-true (BoolValue? bl))
     (for/list ([k (set->list (lookup-store store k-addr))])
       (State (BoolValue) env store (Cont-k k) (tick s)))]
    ; If
    [(State (If tst thn els) env store k t)
     (define k-addr (alloc s))
     (define new-store (ext-store store k-addr (Cont k)))
     (define new-k (DoIfK thn els k-addr))
     (list (State tst env new-store new-k (tick s)))]
    ; If: evaluate test
    [(State tst env store (DoIfK thn els k-addr) t)
     (check-true (BoolValue? tst))
     (append (for/list ([k (set->list (lookup-store store k-addr))])
               (State thn env store (Cont-k k) (tick s)))
             (for/list ([k (set->list (lookup-store store k-addr))])
               (State els env store (Cont-k k) (tick s))))]
    ; Anything else  
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
    [`(if ,tst ,thn ,els)
     (If (parse tst) (parse thn) (parse els))]
    [`(lambda ,label (,var) ,body) (Lam label var (parse body))]
    [`(lambda (,var) ,body) (Lam (gensym 'λ) var (parse body))]
    [`(let ((,lhs ,rhs)) ,body) (App (Lam (gensym 'let) lhs (parse body)) (parse rhs))]
    [`(,rator ,rand) (App (parse rator) (parse rand))]))

; TODO: may has multiple
(define (find-lambda-type label)
  (first (map cdr (filter (λ (item) (symbol=? (Callsite-label (car item)) label)) (hash->list call2type)))))

(define (primitive->string t)
  (match t
    [(BoolValue) "bool"]
    [(IntValue) "int"]
    [(Lam label arg body)
     (arrow-type->string (find-lambda-type label))]
    [_ (error 'primitve->string "not primitive type")]))

(define (arrow-type->string t)
  (match t
    [(ArrowType arg ret)
     (string-append (primitive->string arg)
                    " -> "
                    (if (= 1 (set-count ret))
                        (primitive->string (set-first ret))
                        (string-append "(" (string-join (set-map ret primitive->string)) ")")))]))
     
(module+ test
  (check-equal? (ext-store mt-store 1 'a)
                (hash 1 (set 'a)))
  (check-equal? (ext-store (ext-store mt-store 1 'a) 1 'b)
                (hash 1 (set 'a 'b)))
  (check-equal? (ext-store (ext-store (ext-store mt-store 1 'a) 1 'b) 2 'c)
                (hash 1 (set 'a 'b) 2 (set 'c))))

;(parse '{{lambda {x} x} {lambda {y} y}})
;(parse '{let ([x 1]) x})
;(aval (App (Lam "x" (Var "x")) (Lam "y" (Var "y"))))
;(aval (Lam "x" (Var "x")))
;(aval (parse '{if true 3 4}))
;(aval (parse '{if true 3 false}))

;(aval (parse '{{lambda {x} x} {lambda {y} y}}))
;(aval (parse '{{lambda fz {z} z} {{lambda fx {x} x} {lambda fy {y} y}}}))
;(aval (parse '{lambda {x} x}))
;(aval (parse '{lambda {x} x}))
;(aval (parse 3))
;(aval (parse 'true))
;(aval (parse 'false))

;(aval (parse '{+ 1 2}))
;(aval (parse '{{lambda {x} x} 1}))
;(aval (parse '{and true false}))
;(aval (parse '{or true false}))
;(aval (parse '{not true}))

;(define s1 (aval (parse '{+ 1 {{lambda add1 {x} {+ x 1}} 2}})))
;(define s2 (aval (parse '{+ {{lambda add2 {x} {+ x 2}} 2} 2})))
(define s3 (aval (parse '{{{lambda {x} {lambda {y} {and x y}}} true} false})))

#;
(define s4 (aval (parse '{let {[f {lambda id {x} x}]}
                           {f 1}})))

#;
(define s5 (aval (parse '{let {[id {lambda id {x} x}]}
                           {let {[one {id 1}]}
                             {let {[fls {not {id true}}]}
                               fls}}})))

;(define s6 (aval (parse '{{lambda {x} {not x}} true})))

;(define s7 (aval (parse '{{lambda intorbool {x} {if x 2 true}} false})))

(hash-for-each call2type
               (λ (key type)
                 (let ([label (Callsite-label key)])
                   (if (not (string-prefix? (symbol->string label) "let"))
                       (printf "~a has type: ~a\n" (Callsite-label key) (arrow-type->string type))
                       (void)))))