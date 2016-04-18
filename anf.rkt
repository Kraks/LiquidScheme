#lang racket

; TODO callcc
; TODO logic operation actually allows non-boolean values
; TODO do actual computation instead of using `all-bools`

(require rackunit)
(require "pred.rkt")
(require "parsers.rkt")
(require "structs.rkt")

(provide aval
         aval-infer
         call2type)

#|
 lam ::= (λ (var) exp)

 aexp ::= lam
       |  var
       |  true  |  false
       |  integer
       |  (prim aexp*)

 cexp ::= (aexp0 aexp1)
       |  (if aexp exp exp)
       |  (letrec ((var aexp)) exp)

 exp ::= aexp
      |  cexp
      |  (let ((var exp)) exp)

 prim ::= +  |  -  |  *  |  = | and | or | not
|#

(struct Let (var val body) #:transparent)
(struct Letrec (var val body) #:transparent)
(struct LetK (var body env addr) #:transparent)
(struct EndK (label arg addr) #:transparent)

(struct State (exp env kont time) #:transparent)

(define (parse exp)
  (match exp
    ['true (Bool (True))]
    ['false (Bool (False))]
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
    [`(if ,tst ,thn ,els) (If (parse tst) (parse thn) (parse els))]
    [`(,(or 'lambda 'λ) ,label (,var) ,body) (Lam label var (parse body))]
    [`(,(or 'lambda 'λ) (,var) ,body) (Lam (gensym 'λ) var (parse body))]
    [`(let ((,lhs ,rhs)) ,body) (Let lhs (parse rhs) (parse body))]
    [`(letrec ((,lhs ,rhs)) ,body) (Letrec lhs (parse rhs) (parse body))]
    [`(,rator ,rand) (App (parse rator) (parse rand))]))

; label -> set(ArrowType)
(define call2type (make-hash))

; Currently using 1-CFA
(define k (make-parameter 1))

(define (tick s)
  (take (cons (State-exp s) (State-time s)) (k)))

(define (valid-value? v)
  (match v
    [(? IntValue?) #t]
    [(? BoolValue?) #t]
    [(? VoidValue?) #t]
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

(define store (make-hash))

; lookup-store : store addr -> Set(value)
(define (lookup-store addr)
  (hash-ref store addr d-bot))

; update-store* : store adddr Set(val) -> store
(define (update-store!* addr vals)
  (hash-update! store addr
               (λ (d) (set-union d vals))
               d-bot))

; update-store : store addr val -> store
(define (update-store! addr val)
  (update-store!* addr (set val)))

; store-join : store store -> store
#;
(define (store-join s1 s2)
  (for/fold ([new-store s1])
            ([(k v) (in-hash s2)])
    (update-store* new-store k v)))

; set set (a a -> set) -> set
(define (do-for-all-pairs s1 s2 op)
  (foldl set-union (set)
         (flatten (for/list ([lv s1])
                    (for/list ([rv s2])
                      (op lv rv))))))

; expr env store -> set
(define (eval-prim e env store)
  (match e
    [(Plus l r)
     (do-for-all-pairs (eval-atom l env store)
                       (eval-atom r env store)
                       int/+)]
    [(Minus l r)
     (do-for-all-pairs (eval-atom l env store)
                       (eval-atom r env store)
                       int/-)]
    [(Mult l r)
     (do-for-all-pairs (eval-atom l env store)
                       (eval-atom r env store)
                       int/*)]
    [(And l r)
     (do-for-all-pairs (eval-atom l env store)
                       (eval-atom r env store)
                       bool/and)]
    [(Or l r)
     (do-for-all-pairs (eval-atom l env store)
                       (eval-atom r env store)
                       bool/or)]
    [(NumEq l r)
     (do-for-all-pairs (eval-atom l env store)
                       (eval-atom r env store)
                       int/eq)]
    [(Not b) (bool/not b)]
    [else 'eval-prim "not a primitive operator"]))

; expr env store -> set
(define (eval-atom e env store)
  (match e
    [(Int pred) (set (IntValue pred))]
    [(Bool pred) (set (BoolValue pred))]
    [(Void) (set (VoidValue))]
    [(? prim?) (eval-prim e env store)]
    [(Var x) (lookup-store (lookup-env env x))]
    [(Lam label x body) (set (Clo (Lam label x body) env))]
    [else (error 'eval-atom "not an atom expression")]))

(define (prim? e)
  (match e
    [(Plus _ _) #t]
    [(Minus _ _) #t]
    [(Mult _ _) #t]
    [(And _ _) #t]
    [(Or _ _) #t]
    [(Not _) #t]
    [(NumEq _ _) #t]
    [else #f]))

(define (atom? e)
  (match e
    [(Int _) #t]
    [(Bool _) #t]
    [(Void) #t]
    [(Var _) #t]
    [(Lam _ _ _) #t]
    [(? prim? e) #t]
    [else #f]))

; step : state -> [state]
(define (step s)
  ;(printf "~a\n" s)
  (define time* (tick s))
  (define nexts
    (match s
      [(State (? atom? e) env k t)
       (for/list ([v (set->list (eval-atom e env store))])
         (State v env k time*))]
      [(State (Let var val body) env k t)
       (define k-addr (KAddr (Let var val body) t))
       (define new-k (LetK var body env k-addr))
       (update-store! k-addr (Cont k))
       (list (State val env new-k time*))]
      [(State (? valid-value? val) env (LetK var body env* k-addr) t)
       (define v-addr (BAddr var t))
       (define new-env (ext-env env* var v-addr))
       (update-store! v-addr val)
       (for/list ([k (set->list (lookup-store k-addr))])
         (State body new-env (Cont-k k) time*))]
      [(State (Letrec var val body) env k t)
       (define v-addr (BAddr var t))
       (define new-env (ext-env env var v-addr))
       (define v (eval-atom val new-env store))
       (update-store!* v-addr v)
       (list (State body new-env k t))]
      [(State (App fun arg) env k t)
       (define fun-vs (eval-atom fun env store))
       (for/list ([fun-v (set->list fun-vs)])
         (match fun-v
           [(Clo (Lam label x body) env*)
            (define arg-v (eval-atom arg env store))
            (define v-addr (BAddr x t))
            (define new-env (ext-env env* x v-addr))
            (define new-store (update-store!* v-addr arg-v))
            (define new-k (EndK label arg-v k))
            (State body new-env new-k time*)]
           [else (error 'state "not a closure: ~a" fun-v)]))]

      [(State (? valid-value? e) env (EndK label arg-v next-k) t)
       (hash-update! call2type label
                     (λ (d) (set-union d (set (TArrow arg-v e))))
                     (set))
       (list (State e env next-k t))]
      
      ; If
      [(State (If tst thn els) env k t)
       (for/list ([b (eval-atom tst env store)])
         (match b
           [(BoolValue (True)) (State thn env k time*)]
           [(BoolValue (False)) (State els env k time*)]))]
      ; Anything else
      [s (list s)]))
  ; return next states
  nexts)

(define (inject e)
  (State e mt-env (DoneK) '()))

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
    [#t "any"]
    [(True) "true"]
    [(False) "false"]
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
              (if (= 1 (set-count (TArrow-arg type)))
                  (value->string (set-first (TArrow-arg type)))
                  (string-append "(" (string-join (map value->string (set->list (TArrow-arg type)))) ")"))
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

;(aval-infer (parse '{{lambda add1 {x} {+ x 1}} 2}))

;(aval-infer (parse '{{lambda if {x} {if x true 2}} true}))

#;
(aval-infer (parse '{let {{add1 {lambda add1 {x} {+ x 1}}}}
                      {let {{one {add1 0}}}
                        {let {{two {add1 one}}}
                          {+ one two}}}}))

(define toten (parse '{letrec {{toten {λ toten {n}
                                        {let {{tst {= n 2}}}
                                          {if tst
                                              false
                                              {toten {+ n 1}}}}}}}
                        {toten 1}}))
;(aval-infer toten)

;(aval-infer (parse '{{lambda lamx {x} x} {lambda lamy {y} y}}))

#;
(aval-infer (parse '{let {[id {lambda id {x} x}]}
                      {let {[one {id 1}]}
                        {let {[t {id true}]}
                          {let {[fls {not t}]}
                            fls}}}}))

(define standard-example
  (parse
   '{let {{id {lambda id {x} x}}}
      {let {{a {id {lambda lamz {z} z}}}}
        {let {{b {id {lambda lamy {y} y}}}}
          b}}}))

;(aval-infer standard-example)

(define add1-h (parse '{let {{add1 {lambda add1 {x} {+ 1 x}}}}
                         {let {{apply {lambda lamf {f} {lambda lamg {g} {f g}}}}}
                           {let {{another_add1 {apply add1}}}
                             {another_add1 1}}}}))
(aval-infer add1-h)