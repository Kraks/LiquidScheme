#lang racket

(require srfi/1)
(require rackunit)
(require "structs.rkt")
(require "pred.rkt")

(provide parse
         define-types->hash)

(define (define-types->hash t-defs)
  (define (merge-define-types define-types)
    (define (aux dt lst)
      (define dname (DefineType-name dt))
      (define dtype (DefineType-type dt))
      (define exist-type (assoc dname lst))
      (define dtypes (if exist-type
                         (set-add (cdr exist-type) dtype)
                         (set dtype)))
      (define idx (list-index (curry equal? exist-type) lst))
      (if idx
          (list-set lst idx (cons dname dtypes))
          (cons (cons dname dtypes) lst)))
    (foldl aux
           '()
           define-types))
  (define h (make-hash (merge-define-types (map parse-type-def t-defs))))
  (for/hash ([k (hash-keys h)])
            (let* ([val (hash-ref h k)]
                   [len (length (set->list val))])
              (values k (if (= len 1)
                            (set (set-first val))
                            ;(TIs val)
                            val)))))

(define (parse-type-def tdef)
  (define (parse-type exp)
    (match exp
      [(? integer?) (pred-preprocess (IntValue exp))]
      ['Int (pred-preprocess (IntValue #t))]
      ['Bool (BoolValue #t)]
      ['Any (TAny)]
      ['_ (PSelf)]
      ['true (BoolValue (True))]
      ['false (BoolValue (False))]
      [`(-> ,in-type ,out-type)
       (let* ([it (parse-type in-type)]
              [ot (parse-type out-type)]
              [fit (if (set? it)
                       it
                       (set it))]
              [fot (if (set? ot)
                       ot
                       (set ot))])
         (TArrow fit fot))]
      [`(Int ,pred) (pred-preprocess (IntValue (parse-pred pred)))]
      [`(Bool ,pred) (BoolValue (parse-pred pred))]))
  (match tdef
    [`(: ,name ,type) (DefineType name (parse-type type))]
    [_ (error 'parse-type-def "not a type definition")]))

(define (desugar-pred pred)
  (match pred
    [`(>= ,e1 ,e2) (desugar-pred `(or (> ,e1 ,e2) (= ,e2 ,e1)))]
    [`(<= ,e1 ,e2) (desugar-pred `(or (> ,e2 ,e1) (= ,e2 e1)))]
    [`(!= ,e1 ,e2) `(not (= ,e1 ,e2))]
    [`(< ,e1 ,e2)  `(>  ,e2 ,e1)]
    [e e]))

(define (parse-pred pred)
  (let ([d-pred (desugar-pred pred)])
    (match d-pred
      ['true (True)]
      ['false (False)]
      ['_ (PSelf)]
      [(? integer?) d-pred #;(PInt d-pred)]
      [(? symbol?) (PVar d-pred)]
      [`(+ ,lhs ,rhs) (PPlus (parse-pred lhs) (parse-pred rhs))]
      [`(- ,lhs ,rhs) (PMinus (parse-pred lhs) (parse-pred rhs))]
      [`(* ,lhs ,rhs) (PMult (parse-pred lhs) (parse-pred rhs))]
      [`(= ,lhs ,rhs) (PNumEq (parse-pred lhs) (parse-pred rhs))] ;; var to the left of =
      [`(and ,lhs ,rhs) (PAnd (parse-pred lhs) (parse-pred rhs))]
      [`(or ,lhs ,rhs) (POr (parse-pred lhs) (parse-pred rhs))]
      [`(not ,bl) (PNot (parse-pred bl))]
      [`(> ,lhs ,rhs) (PGreater (parse-pred lhs) (parse-pred rhs))]
      [_ (error 'parse-pred "unknown predicate ~a" pred)])))

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
    [`(set! ,var ,val) (Set var (parse val))]
    [`(if ,tst ,thn ,els) (If (parse tst) (parse thn) (parse els))]
    [`(begin ,s1 ,s2) (Begin (parse s1) (parse s2))]
    [`(,(or 'lambda 'λ) ,label (,var) ,body) (Lam label var (parse body))]
    [`(,(or 'lambda 'λ) (,var) ,body) (Lam (gensym 'λ) var (parse body))]
    [`(let ((,lhs ,rhs)) ,body) (App (Lam (gensym 'let) lhs (parse body)) (parse rhs))]
    [`(letrec ((,lhs ,rhs)) ,body)
     (parse `(let ((,lhs (void)))
               (begin (set! ,lhs ,rhs)
                      ,body)))]
    [`(,rator ,rand) (App (parse rator) (parse rand))]))


;; TODO:
; below:  pred-processing preds

;; TESTS
(module+ test
  (define h (define-types->hash
              '((: a (-> Int Int))
                (: b (-> Int Int))
                (: c (-> Int Int))
                (: c (-> Bool Bool)))))
  (check-equal? h
                (hash 'a
                      (set (TArrow (set (IntValue #t)) (set (IntValue #t))))
                      'c
                      (set (TArrow (set (IntValue #t)) (set (IntValue #t)))
                           (TArrow (set (BoolValue #t)) (set (BoolValue #t))))
                      'b
                      (set (TArrow (set (IntValue #t)) (set (IntValue #t))))))
  
  (define hh (define-types->hash
               '((: abs (-> (Int (and 3 (or (> _ 8) (< _ 18)))) (Int (> _ 1)))))))
  
  (check-equal? hh
                (hash 'abs (set (TArrow (set (IntValue 3)) (set (IntValue (PGreater (PSelf) 1)))))))
  )


; hash: symbol -> Set(TArrow)
; TArrow Set(Value) Set(Value)