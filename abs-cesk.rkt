#lang racket

; TODO add test cases

(require rackunit)

(struct State (exp env store kont time) #:transparent)

; Exp
(struct Var (name) #:transparent)
(struct Lam (label var exp) #:transparent)
(struct App (fun arg) #:transparent)
(struct Int () #:transparent)
(struct Bool () #:transparent)
(struct Plus (lhs rhs) #:transparent)
(struct Minus (lhs rhs) #:transparent)
(struct Mult (lhs rhs) #:transparent)
(struct And (lhs rhs) #:transparent)
(struct Or (lhs rhs) #:transparent)
(struct Not (bl) #:transparent)
(struct Set (var val) #:transparent)
(struct If (tst thn els) #:transparent)
(struct Begin (s1 s2) #:transparent)
(struct Void () #:transparent)
(struct NumEq (lhs rhs) #:transparent)

; Continuation
(struct DoneK () #:transparent)
(struct ArgK (exp env addr) #:transparent)
(struct AppK (lam env addr) #:transparent)
(struct PlusK (r env store addr) #:transparent)
(struct DoPlusK (l addr) #:transparent)
(struct MinusK (r env store addr) #:transparent)
(struct DoMinusK (l addr) #:transparent)
(struct MultK (r env store addr) #:transparent)
(struct DoMultK (l addr) #:transparent)
(struct AndK (r env store addr) #:transparent)
(struct DoAndK (l addr) #:transparent)
(struct OrK (r env store addr) #:transparent)
(struct DoOrK (l addr) #:transparent)
(struct DoNotK (addr) #:transparent)
(struct DoIfK (thn els addr) #:transparent)
(struct SetK (var addr) #:transparent)
(struct BeginK (s2 addr) #:transparent)
(struct NumEqK (r env store addr) #:transparent)
(struct DoNumEqK (l addr) #:transparent)

; Storable / Value
(struct Clo (lam env) #:transparent)
(struct Cont (k) #:transparent)
(struct IntValue () #:transparent)
(struct BoolValue () #:transparent)
(struct VoidValue () #:transparent)

; Address
(struct BAddr (var time) #:transparent)
(struct KAddr (exp time) #:transparent)

; Currently using 0-CFA
(define k (make-parameter 0))

(define (tick s)
  (take (cons (State-exp s) (State-time s)) (k)))

(struct Callsite (label k) #:transparent)
(struct ArrowType (arg ret) #:transparent)

(define (atomic-value? v)
  (match v
    [(? IntValue?) #t]
    [(? BoolValue?) #t]
    [(? VoidValue?) #t]
    [_ #f]))

(define (valid-value? v)
  (match v
    [(? Lam?) #t] ;TODO reconsider
    [(? atomic-value?) #t]
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

; step : state hashtable hashtable -> ([state] hashtable hashtable)
(define (step s cont2label call2type)
  (define nexts
    (match s
      ; Int
      [(State (Int) env store k t)
       (list (State (IntValue) env store k (tick s)))]
      ; Bool
      [(State (Bool) env store k t)
       (list (State (BoolValue) env store k (tick s)))]
      ; Void
      [(State (Void) env store k t)
       (list (State (VoidValue) env store k (tick s)))]
      ; Ref
      [(State (Var x) env store k t)
       (for/list ([val (set->list (lookup-store store (lookup-env env x)))])
         (cond [(Clo? val) (State (Clo-lam val) (Clo-env val) store k (tick s))]
               [else (State val env store k (tick s))]))]
      ; Application
      [(State (App fun arg) env store k t)
       (define k-addr (KAddr (App fun arg) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (ArgK arg env k-addr))
       (list (State fun env new-store new-k (tick s)))]
      ; Application: evaluate argument
      [(State (Lam label var exp) env store (ArgK e k-env k-addr) t)
       (list (State e k-env store (AppK (Lam label var exp) env k-addr) (tick s)))]
      ; Application: evaluate callee and into the body of function
      [(State (? valid-value? exp) env store (AppK (Lam label x e) k-env k-addr) t)
       ; TODO, check the exp should only be a lambda
       (define val
         (cond [(Lam? exp) (Clo exp env)]
               [else exp]))
       (define v-addr (BAddr x t))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State e (ext-env k-env x v-addr) (ext-store store v-addr val) (Cont-k k) (tick s)))]
      ; Plus
      [(State (Plus l r) env store k t)
       (define k-addr (KAddr (Plus l r) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (PlusK r env new-store k-addr))
       (list (State l env new-store new-k (tick s)))]
      ; Plus: after evaluate left hand side
      [(State (? valid-value? l) env store (PlusK r r-env r-store k-addr) t)
       (check-true (IntValue? l))
       (list (State r r-env r-store (DoPlusK l k-addr) (tick s)))]
      ; Plus: after evaluate right hand side
      [(State (? valid-value? r) env store (DoPlusK l k-addr) t)
       (check-true (IntValue? r))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (IntValue) env store (Cont-k k) (tick s)))]
      ; Minus
      [(State (Minus l r) env store k t)
       (define k-addr (KAddr (Minus l r) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (MinusK r env new-store k-addr))
       (list (State l env new-store new-k (tick s)))]
      ; Minus: after evaluate left hand side
      [(State (? valid-value? l) env store (MinusK r r-env r-store k-addr) t)
       (check-true (IntValue? l))
       (list (State r r-env r-store (DoMinusK l k-addr) (tick s)))]
      ; Minus: after evaluate right hand side
      [(State (? valid-value? r) env store (DoMinusK l k-addr) t)
       (check-true (IntValue? r))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (IntValue) env store (Cont-k k) (tick s)))]
      ; Mult
      [(State (Mult l r) env store k t)
       (define k-addr (KAddr (Mult l r) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (MultK r env new-store k-addr))
       (list (State l env new-store new-k (tick s)))]
      ; Mult: after evaluate left hand side
      [(State (? valid-value? l) env store (MultK r r-env r-store k-addr) t)
       (check-true (IntValue? l))
       (list (State r r-env r-store (DoMultK l k-addr) (tick s)))]
      ; Mult: after evaluate right hand side
      [(State (? valid-value? r) env store (DoMultK l k-addr) t)
       (check-true (IntValue? r))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (IntValue) env store (Cont-k k) (tick s)))]
      ; NumEq
      [(State (NumEq l r) env store k t)
       (define k-addr (KAddr (NumEq l r) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (NumEqK r env new-store k-addr))
       (list (State r env new-store new-k (tick s)))]
      ; NumEq: after evaluate left hand side
      [(State (? valid-value? l) env store (NumEqK r r-env r-store k-addr) t)
       (check-true (IntValue? l))
       (list (State r r-env r-store (DoNumEqK l k-addr) (tick s)))]
      ; NumEq: after evaluate right hand side
      [(State (? valid-value? r) env store (DoNumEqK l k-addr) t)
       (check-true (IntValue? r))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (BoolValue) env store (Cont-k k) (tick s)))]
      ; Logic and
      ; TODO logic operation actually allows non-boolean values
      [(State (And l r) env store k t)
       (define k-addr (KAddr (And l r) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (AndK r env new-store k-addr))
       (list (State l env new-store new-k (tick s)))]
      ; Logic and: after evaluate left hand side
      [(State (? valid-value? l) env store (AndK r r-env r-store k-addr) t)
       (check-true (BoolValue? l))
       (cons (State r r-env r-store (DoAndK l k-addr) (tick s))
             (for/list ([k (set->list (lookup-store store k-addr))])
               (State (BoolValue) env store (Cont-k k) (tick s))))]
      ; Logic and: after evaluate right hand side
      [(State (? valid-value? r) env store (DoAndK l k-addr) t)
       (check-true (BoolValue? r))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (BoolValue) env store (Cont-k k) (tick s)))]
      ; Logic or
      [(State (Or l r) env store k t)
       (define k-addr (KAddr (Or l r) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (OrK r env new-store k-addr))
       (list (State l env new-store new-k (tick s)))]
      ; Logic or: after evaluate left hand side
      [(State (? valid-value? l) env store (OrK r r-env r-store k-addr) t)
       (check-true (BoolValue? l))
       (cons (State r r-env r-store (DoOrK l k-addr) (tick s))
             (for/list ([k (set->list (lookup-store store k-addr))])
               (State (BoolValue) env store (Cont-k k) (tick s))))]
      ; Logic or: after evaluate right hand side
      [(State (? valid-value? r) env store (DoOrK l k-addr) t)
       (check-true (BoolValue? r))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (BoolValue) env store (Cont-k k) (tick s)))]
      ; Logic not
      [(State (Not b) env store k t)
       (define k-addr (KAddr (Not b) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (DoNotK k-addr))
       (list (State b env new-store new-k (tick s)))]
      ; Logic not: after evaluate the expr
      [(State (? valid-value? b) env store (DoNotK k-addr) t)
       (check-true (BoolValue? b))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (BoolValue) env store (Cont-k k) (tick s)))]
      ; If
      [(State (If tst thn els) env store k t)
       (define k-addr (KAddr (If tst thn els) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (DoIfK thn els k-addr))
       (list (State tst env new-store new-k (tick s)))]
      ; If: after evaluate the condition
      [(State (? valid-value? tst) env store (DoIfK thn els k-addr) t)
       (check-true (BoolValue? tst))
       (append (for/list ([k (set->list (lookup-store store k-addr))])
                 (State thn env store (Cont-k k) (tick s)))
               (for/list ([k (set->list (lookup-store store k-addr))])
                 (State els env store (Cont-k k) (tick s))))]
      ; Set!
      [(State (Set var val) env store k t)
       (define k-addr (KAddr (Set var val) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (SetK var k-addr))
       (list (State val env new-store (SetK var k-addr) (tick s)))]
      ; SetK
      [(State (? valid-value? val) env store (SetK var k-addr) t)
       ; TODO Just set the store? or need to join the set? need to reconsider.
       (define new-store (hash-set store (lookup-env env var) (set val)))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State (VoidValue) env new-store (Cont-k k) (tick s)))]
      ; Begin
      [(State (Begin s1 s2) env store k t)
       (define k-addr (KAddr (Begin s1 s2) t))
       (define new-store (ext-store store k-addr (Cont k)))
       (define new-k (BeginK s2 k-addr))
       (list (State s1 env new-store new-k (tick s)))]
      ; BeginK: after evaluate the first expression
      [(State (? valid-value? s1) env store (BeginK s2 k-addr) t)
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State s2 env store (Cont-k k) (tick s)))]
      ; Anything else
      [s (list s)]))
  ; If the current continuation we have saved in the cont2label, which means
  ; now it finished eval the body of a function and will return to that continuation,
  ; then we put the (State-exp s) as the return type of function and save to hash table.
  (if (and (hash-has-key? cont2label (State-kont s))
           (valid-value? (State-exp s)))
      (let* ([label (hash-ref cont2label (State-kont s))]
             [cur-type (hash-ref call2type (Callsite label (State-kont s)))])
        (hash-set! call2type (Callsite label (State-kont s))
                   (ArrowType (ArrowType-arg cur-type)
                              ; Note: the actual returned value should be Closure if the (State-exp s) is a Lambda
                              (set-union (ArrowType-ret cur-type) (set (State-exp s))))))
      (void))
  ; If we see an AppK continuation, then it will go into the function body
  ; so we save argument type info and where it will return to
  (match s
    [(State (? valid-value? exp) env store (AppK (Lam label x e) k-env k-addr) t)
     (for/list ([k (set->list (lookup-store store k-addr))])
       (hash-set! cont2label (Cont-k k) label)
       (hash-set! call2type (Callsite label (Cont-k k)) (ArrowType exp (set))))]
    [_ (void)])
  ; return next states, cont2label and call2type
  (values nexts cont2label call2type))

(define (inject e)
  (State e mt-env mt-store (DoneK) '()))

(define (explore f init)
  (search f (set) (list init) (make-hash) (make-hash)))

(define (search f seen todo cont2label call2type)
  (cond [(empty? todo) (values seen cont2label call2type)]
        [(set-member? seen (first todo))
         (search f seen (cdr todo) cont2label call2type)]
        [else (let-values ([(nexts cont2label call2type) (f (first todo) cont2label call2type)])
                (search f
                        (set-add seen (first todo))
                        (append nexts (cdr todo))
                        cont2label
                        call2type))]))

; exp -> [State]
(define (aval e)
 (let-values ([(states cont2type call2type) (explore step (inject e))])
   states))

; TODO: may has multiple
;(define (find-lambda-type label)
;  (first (map cdr (filter (λ (item) (symbol=? (Callsite-label (car item)) label)) (hash->list call2type)))))

(define (primitive->string t)
  (match t
    [(BoolValue) "bool"]
    [(IntValue) "int"]
    [(VoidValue) "void"]
    [(Lam label arg body) (string-append "lambda " (symbol->string label))]
     ;(arrow-type->string (find-lambda-type label))]
    [_ (error 'primitve->string "not primitive type")]))

(define (arrow-type->string t)
  (match t
    [(ArrowType arg ret)
     (string-append (primitive->string arg)
                    " -> "
                    (if (= 1 (set-count ret))
                        (primitive->string (set-first ret))
                        (string-append "(" (string-join (set-map ret primitive->string)) ")")))]))

; TODO: can be remove
(define (sort-state-set states)
  (sort (set->list states) < #:key State-time))

(define (aval-infer e)
  (let-values ([(states cont2label call2type) (explore step (inject e))])
    (extract-func-type cont2label call2type)))

(define (extract-func-type cont2label call2type)
  (hash-for-each call2type
                 (λ (key type)
                   (let ([label (Callsite-label key)])
                     (if (not (string-prefix? (symbol->string label) "let"))
                         (printf "~a has type: ~a\n" (Callsite-label key) (arrow-type->string type))
                         (void))))))

(define (parse exp)
  (match exp
    ['true (Bool)]
    ['false (Bool)]
    ['(void) (Void)]
    [(? integer?) (Int)]
    [(? symbol?) (Var exp)]
    [`(+ ,lhs ,rhs) (Plus (parse lhs) (parse rhs))]
    [`(- ,lhs ,rhs) (Minus (parse lhs) (parse rhs))]
    [`(* ,lhs ,rhs) (Mult (parse lhs) (parse rhs))]
    [`(= ,lhs ,rhs) (NumEq (parse lhs) (parse rhs))]
    [`(and ,lhs ,rhs) (And (parse lhs) (parse rhs))]
    [`(or ,lhs ,rhs) (Or (parse lhs) (parse rhs))]
    [`(not ,bl) (Not (parse bl))]
    [`(set! ,var ,val) (Set var (parse val))]
    [`(if ,tst ,thn ,els) (If (parse tst) (parse thn) (parse els))]
    [`(begin ,s1 ,s2) (Begin (parse s1) (parse s2))]
    [`(lambda ,label (,var) ,body) (Lam label var (parse body))]
    [`(lambda (,var) ,body) (Lam (gensym 'λ) var (parse body))]
    [`(let ((,lhs ,rhs)) ,body) (App (Lam (gensym 'let) lhs (parse body)) (parse rhs))]
    [`(letrec ((,lhs ,rhs)) ,body)
     (parse `(let ((,lhs (void)))
               (begin (set! ,lhs ,rhs)
                      ,body)))]
    [`(,rator ,rand) (App (parse rator) (parse rand))]))

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

#;
(define s3 (aval (parse '{let {[id {lambda id {x} x}]}
                           {let {[one {id 1}]}
                             {let {[fls {not {id true}}]}
                               fls}}})))
#;
(define s4 (aval (parse '{{{lambda {x} {lambda {y} {and x y}}} true} false})))

#;
(define s6 (aval (parse '{let {[f {lambda id {x} x}]}
                           {f 1}})))

;(define s7 (aval (parse '{{lambda intorbool {x} {if x 2 true}} false})))

;(define s8 (aval (parse '{{lambda {x} {not x}} true})))

;(define s9 (aval (parse '{{{{lambda {x} {lambda {i} {lambda {j} {if x i j}}}} true} 1} 2})))
;(define s10 (aval (parse '{begin {+ 1 2} {+ 3 4}})))

;(aval (parse '{or {not true} false}))
;(aval (parse '{+ {if true 1 2} 3}))

#;
(define s11 (aval (parse '{let {{a 1}}
                            {begin {set! a true}
                                   a}})))

#;
(define s12 (aval (parse '{letrec {{a {lambda {x} a}}} a})))

(define s13 (aval (parse '{let {{fact {void}}}
                                   {begin {set! fact {lambda fact {n} {if {= n 0} 1 {* n {fact {- n 1}}}}}}
                                          {fact 5}}})))

;(aval (parse '{letrec {{fact {lambda fact {n} {if {= n 0} 1 {* n {fact {- n 1}}}}}}} {fact 5}}))

;(define s14 (aval (parse '{if {= 1 2} 2 3})))
