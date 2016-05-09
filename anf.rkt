#lang racket

; TODO callcc
; TODO logic operation actually allows non-boolean values
; TODO do actual computation instead of using `all-bools`
; TODO:
#|
abs: 
    int[-2] -> int[2]
    int[1] -> int[1]
"Done"
> call2type
(hash 'abs (set (TArrow (set (IntValue -2)) (IntValue 2)) (TArrow (set (IntValue 1)) (IntValue 1))))
|#
; TODO: if
; TODO: z3

(require rackunit)
(require srfi/1)
(require "pred.rkt")
(require "parsers.rkt")
(require "structs.rkt")

(provide aval
         aval-infer
         call2type
         verify-contract
         verify-runtime)

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
    [(Greater l r)
     (do-for-all-pairs (eval-atom l env store)
                       (eval-atom r env store)
                       int/>)]
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
    [(Greater _ _) #t]
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
            (define arg-vs (eval-atom arg env store))
            (define v-addr (BAddr x t))
            (define new-env (ext-env env* x v-addr))
            (define new-store (update-store!* v-addr arg-vs))
            (define new-k (EndK label arg-vs k))
            (State body new-env new-k time*)]
           [else (error 'state "not a closure: ~a" fun-v)]))]

      [(State (? valid-value? e) env (EndK label arg-vs next-k) t)
       (hash-update! call2type label
                     (λ (d) (set-union d (set (TArrow arg-vs (set e)))))
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

(define (pred->string p)
  (match p
    [#t "any"]
    [(True) "true"]
    [(False) "false"]
    [(? number?) (number->string p)]
    [(PGreater (PSelf) (? number? n)) (string-append ">" (number->string n))]
    [(PGreater (? number? n) (PSelf)) (string-append "<" (number->string n))]
    [(PGreater (PVar var) (? number? n))
     (string-append (symbol->string var) ">" (number->string n))]
    [(PGreater (? number? n) (PVar var))
     (string-append (symbol->string var) "<" (number->string n))]
    [(PAnd l r)
     (string-append "(and" (pred->string l) " " (pred->string r) ")")]
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
  (hash-clear! store)
  (explore step (inject e))
  (for/list ([(label types) (in-hash call2type)])
    (printf "~a: \n" label)
    (for/set ([type types])
      (printf "    ~a -> ~a\n"
              (if (= 1 (set-count (TArrow-arg type)))
                  (value->string (set-first (TArrow-arg type)))
                  (string-append "("
                                 (string-join (map value->string (set->list (TArrow-arg type))))
                                 ")"))
              (if (= 1 (set-count (TArrow-ret type)))
                  (value->string (set-first (TArrow-ret type)))
                  (string-append "("
                                 (string-join (map value->string (set->list (TArrow-ret type))))
                                 ")")))))
  (make-hash (hash-map call2type (lambda (key types)
                                   (cons key (set-map types (lambda (type) (TArrow (set-first (TArrow-arg type))
                                                                                   (TArrow-ret type)))))))))


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
                                        {let {{tst {= n 10}}}
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
                         {let {{add2 {lambda add2 {x} {+ 2 x}}}}
                           {let {{apply {lambda applyf {f} {lambda applyg {g} {f g}}}}}
                             {let {{another_add1 {apply add1}}}
                               {let {{another_add2 {apply add2}}}
                                 {let {{two {another_add1 1}}}
                                   {let {{three {another_add1 two}}}
                                     {another_add2 1}}}}}}}}))
;(aval-infer add1-h)

(define abs (parse '{let {{abs {lambda abs {x} {if {> x 0}
                                                   x
                                                   {- 0 x}}}}}
                      {let {{one {abs 1}}}
                        {let {{two {abs {- 0 2}}}}
                          two}}}))
;(aval-infer abs)

(define (replace-self-with-name pred var)
  (match pred
    [(PSelf) (PVar var)]
    [(PGreater l r)
     (PGreater (replace-self-with-name l var) (replace-self-with-name r var))]
    [(PAnd l r)
     (PAnd (replace-self-with-name l var) (replace-self-with-name r var))]
    [p p]))

; Predicate symbol -> s-exp
(define (pred->z3 pred self-name)
  (match pred
    [#t '()]
    [(PVar name) name]
    [(? number? n) `(= ,self-name ,n)]
    [(PAnd l r) `(and ,(pred->z3 l self-name) ,(pred->z3 r self-name))]
    [(PGreater (? number? l) r)
     `(> ,l ,(pred->z3 r self-name))]
    [(PGreater l (? number? r))
     `(> ,(pred->z3 l self-name) ,r)]
    [(PSelf) (error 'pred->z3 "should replace PSelf with first")]))

; Set(Predicate) symbol -> [s-exp]
(define (pred-set->z3 preds self-name)
  (if (= 1 (set-count preds))
      (pred->z3 (set-first preds) self-name)
      `(or ,(set-map preds (λ (pred) (pred->z3 pred self-name))))))

; Value symbol -> [s-exp]
(define (value->z3 val self-name)
  (match val
    [(IntValue pred)
     (append `(declare-const ,self-name Int) '())]
    [(BoolValue pred)
     `(declare-const ,self-name Bool)]
    [(VoidValue) (void)]
    [(Clo (Lam label x body) env) label]
    [_ (error 'value->z3 "not a value")]))

(module+ test
  (check-equal? (replace-self-with-name (PAnd (PGreater (PSelf) 3) (PGreater 5 (PSelf))) 'x)
                (PAnd (PGreater (PVar 'x) 3) (PGreater 5 (PVar 'x))))
  (check-equal? (pred->z3 (PAnd (PGreater (PVar 'x) 3) (PGreater 5 (PVar 'x))) 'x)
                '(and (> x 3) (> 5 x)))
  (check-equal? (pred-set->z3 (set (PAnd (PGreater (PVar 'x) 3) (PGreater 5 (PVar 'x)))) 'x)
                '(and (> x 3) (> 5 x)))
  (check-equal? (pred-set->z3 (set (PAnd (PGreater (PVar 'x) 3) (PGreater 5 (PVar 'x)))
                                   (PAnd (PGreater (PVar 'x) 6) (PGreater 9 (PVar 'x)))) 'x)
                '(or ((and (> x 3) (> 5 x)) (and (> x 6) (> 9 x))))))

(define (transform v)
  (match v
    [(IntValue p) (Int p)]
    [(BoolValue p) (Bool p)]))

; Expr Hash -> Void
(define (reform-tarrow-s2s tarrow-s2s)
  (define arg-tp (TArrow-arg tarrow-s2s))
  (define ret-tp (TArrow-ret tarrow-s2s))
  (apply append (set-map arg-tp
                         (lambda (atp)
                           (TArrow atp ret-tp)))))

(define (is-sub-returns? a-return g-returns)
  (any identity
       (set-map g-returns (lambda (gr) (is-sub-type? a-return gr)))))

; TODO: change name
; TODO: set union
(define (match-returns? return g-returns)
  (ormap (lambda (ar) (is-sub-returns? ar g-returns)) (set->list return)))

(define (verify-contract func contracts)
  (define func-name (Lam-label func))
  (define tarrows (hash-ref contracts func-name))
  (define (aux tarrow)
    (define arg (TArrow-arg tarrow))
    (define call2type (aval-infer (App func (transform arg))))
    (define avaled-tarrows 
      (set-map (hash-ref call2type func-name)
               reform-tarrow-s2s))
    
    (displayln avaled-tarrows)
    (define given-returns (TArrow-ret tarrow))
    (define match-status
      (for/and ([avaled-tarrow avaled-tarrows])
        (define avaled-return (TArrow-ret avaled-tarrow))
        (match-returns? avaled-return given-returns)))
    (when (not match-status)
      (printf "Error: contract violated: ~a\n" func-name)))
  (set-for-each tarrows aux))


; TArrow Set(TArrow) symbol -> Boolean
(define (check-contract instance contracts func-name)
  (define arg (TArrow-arg instance))
  (define ret (TArrow-ret instance))
  (displayln arg)
  (displayln ret)
  ;(printf "~a ~a\n" arg ret)
  (define arg-match-contracts
    (filter (lambda (c) (is-sub-type? arg (begin (TArrow-arg c)))) (set->list contracts)))
  (define compitable-contracts
    (filter (lambda (c) (match-returns? ret (begin (display (TArrow-ret c))
                                                             (TArrow-ret c)))) arg-match-contracts))
  (if (null? compitable-contracts)
      (printf "Error: contract violate: ~a\n" func-name)
      (void)))

; Expr Hash ->
(define (verify-runtime expr contracts)
  (define call2type (aval-infer expr))
  (for ([(label arrows)
         (in-hash call2type)])
    (when (hash-has-key? contracts label)
      (for ([arrow arrows])
        (check-contract arrow (hash-ref contracts label) label)))))