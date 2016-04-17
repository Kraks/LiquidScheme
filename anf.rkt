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

(struct Let (var val body) #:transparent)
(struct LetK (var body env addr) #:transparent)
(struct EndK (label arg addr) #:transparent)

(define (parse exp)
  (match exp
    ['true (Bool #t)]
    ['false (Bool #f)]
    ['(void) (Void)]
    [(? integer? n) (Int n)]
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
    [`(,(or 'lambda 'λ) ,label (,var) ,body) (Lam label var (parse body))]
    [`(,(or 'lambda 'λ) (,var) ,body) (Lam (gensym 'λ) var (parse body))]
    [`(let ((,lhs ,rhs)) ,body) (Let lhs (parse rhs) (parse body))]
    [`(letrec ((,lhs ,rhs)) ,body)
     (parse `(let ((,lhs (void)))
               (begin (set! ,lhs ,rhs)
                      ,body)))]
    [`(,rator ,rand) (App (parse rator) (parse rand))]))

; label -> set(ArrowType)
(define call2type (make-hash))

; Currently using 1-CFA
(define k (make-parameter 0))

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
    [(? Clo?) #t]
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

(define (eval-atom e env store)
  (match e
    [(Int pred) (set (IntValue pred))]
    [(Bool pred) (set (BoolValue pred))]
    [(Void) (set (VoidValue))]
    [(Var x) (lookup-store store (lookup-env env x))]
    [(Lam label x body) (set (Clo (Lam label x body) env))]
    [else (error 'eval-atom "not an atom expression")]))

(define (atom? e)
  (match e
    [(Int _) #t]
    [(Bool _) #t]
    [(Void) #t]
    [(Var _) #t]
    [(Lam _ _ _) #t]
    [else #f]))

; step : state -> [state]
(define (step s)
  (define time* (tick s))
  (define nexts
    (match s
      [(State (? atom? e) env store k t)
       (for/list ([v (set->list (eval-atom e env store))])
         (State v env store k time*))]
      [(State (Let var val body) env store k t)
       (define k-addr (KAddr (Let var val body) t))
       (define new-k (LetK var body env k-addr))
       (define new-store (ext-store store k-addr (Cont k)))
       (list (State val env new-store new-k time*))]
      [(State (? valid-value? val) env store (LetK var body env* k-addr) t)
       (define v-addr (BAddr var t))
       (define new-env (ext-env env* var v-addr))
       (define new-store (ext-store store v-addr val))
       (for/list ([k (set->list (lookup-store store k-addr))])
         (State body new-env new-store (Cont-k k) time*))]
      [(State (App fun arg) env store k t)
       (define fun-vs (eval-atom fun env store))
       (for/list ([fun-v (set->list fun-vs)])
         (match fun-v
           [(Clo (Lam label x body) env*)
            ;TODO FIXME, may have many values
            (define arg-v (set-first (eval-atom arg env store)))
            (define v-addr (BAddr x t))
            (define new-env (ext-env env* x v-addr))
            (define new-store (ext-store store v-addr arg-v))
            (define new-k (EndK label arg-v k))
            (State body new-env new-store new-k time*)]
           [else (error 'state "not a closure")]))]
      [(State (? valid-value? e) env store (EndK label arg-v next-k) t)
       ;(printf "~a: ~a -> ~a\n" label arg-v e)
       (hash-update! call2type
                     label
                     (λ (d) (set-union d (set (TArrow arg-v e))))
                     (set))
       (list (State e env store next-k t))]
      ; Plus
      [(State (Plus l r) env store k t)
       (flatten (for/list ([lv (eval-atom l env store)])
                  (for/list ([rv (eval-atom r env store)])
                    (State (int/+ lv rv) env store k time*))))]
      ; Minus
      [(State (Minus l r) env store k t)
       (list (State (IntValue #t) env store k time*))]
      ; Mult
      [(State (Mult l r) env store k t)
       (list (State (IntValue #t) env store k time*))]
      ; NumEq
      [(State (NumEq l r) env store k t)
       (define result (int/eq l r))
       (for/list ([b result])
         (State b env store k time*))]
      ; Logic and
      ; TODO logic operation actually allows non-boolean values
      ; TODO do actual computation instead of using `bools`
      [(State (And l r) env store k t)
       (define result bools)
       (for/list ([b result])
         (State b env store k time*))]
      ; Logic or
      [(State (Or l r) env store k t)
       (define result bools)
       (for/list ([b result])
         (State b env store k time*))]
      ; Logic not
      [(State (Not b) env store k t)
       (define result bools)
       (for/list ([b result])
         (State b env store k time*))]
      ; If
      [(State (If tst thn els) env store k t)
       (define tst-v bools)
       (for/list ([b tst-v])
         (match b
           [(BoolValue (True)) (State thn env store k time*)]
           [(BoolValue (False)) (State els env store k time*)]))]
      ; Anything else
      [s (list s)]))
  ; return next states
  nexts)

(define (inject e)
  (State e mt-env mt-store (DoneK) '()))

(define (explore f init)
  (search f (set) (list init) 0 (list)))

(define (search f seen todo id result)
  ;(displayln id)
  (cond [(empty? todo) result]
        [(set-member? seen (first todo))
         (search f seen (cdr todo) id result)]
        [else (search f (set-add seen (first todo))
                      (append (f (first todo)) (cdr todo))
                      (add1 id)
                      (cons (cons id (first todo)) result))]))

; exp -> [State]
(define (aval e) (explore step (inject e)))

; TODO
(define (pred->string p)
  (match p
    [(? number?) (number->string p)]
    [else ""]))

(define (value->string e)
  (match e
    [(IntValue pred) (string-append "int[" (pred->string pred) "]")]
    [(BoolValue pred) (string-append "bool[" (pred->string pred) "]")]
    [(VoidValue) "void"]
    [(Clo (Lam label x body) env) (symbol->string label)]
    [else (error 'value->string "not a primitive value")]))

(define (aval-infer e)
  (hash-clear! call2type)
  (explore step (inject e))
  (for/list ([(label types) (in-hash call2type)])
    (printf "~a: \n" label)
    (for/set ([type types])
      (printf "    ~a -> ~a\n"
              (value->string (TArrow-arg type))
              (value->string (TArrow-ret type)))))
  "Done")

;;;;;;;;;;;;;;;;

#;
(aval (parse '{let {{add1 {lambda add1 {x} {+ x 1}}}}
                      {add1 2}}))

#;
(aval-infer (parse '{let {{add {lambda add_x {x}
                                 {lambda add_y {y}
                                   {+ x y}}}}}
                      {let {{add1 {add 1}}}
                        {add1 2}}}))
#;
(aval (parse '{let {{add {lambda add_x {x}
                           {lambda add_y {y}
                             {+ x y}}}}}
                {let {{add1 {add 1}}}
                  {add1 2}}}))

;(aval-infer (parse '{{lambda add1 {x} {+ x 1}} 2}))

;(aval-infer (parse '{{lambda if {x} {if x true 2}} true}))

(aval-infer (parse '{let {{add1 {lambda add1 {x} {+ x 1}}}}
                      {let {{one {add1 0}}}
                        {let {{two {add1 one}}}
                          {+ one two}}}}))

#;
(aval-infer (parse '{{lambda lamx {x} x} {lambda lamy {y} y}}))