#lang racket

(require srfi/1)
(require rackunit)
(require "./structs.rkt")
(require "./syntax.rkt")


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
  (merge-define-types (map parse-type-def t-defs)))


(define (parse-type-def tdef)
  (define (parse-type exp)
    (match exp
      ['Int (TInt #t)]
      ['Bool (TBool #t)]   
      ['Any (TAny #t)] ;; add local type inference if refinement type exists.
      ['true (TBool (True))]
      ['false (TBool (False))]
      [`(-> ,in-type ,out-type) (TArrow (parse-type in-type) (parse-type out-type))]
      [`(Int ,pred) (TInt (parse-pred pred))]
      [`(Bool ,pred) (TBool (parse-pred pred))]
      [(? integer?) (TInt exp)]))
  (match tdef
    [`(: ,name ,type) (DefineType name (parse-type type))]
    [_ (error 'parse-type-def "not a type definition")]))

(define (parse-pred pred)
  (let ([d-pred (desugar pred)])
    (match d-pred
      ['true (True)]
      ['false (error 'parse-pred "can't assign #f/false to predicate")]
      ['(void) (Void)]
      [(? integer?) (PInt d-pred)]
      [(? symbol?) (PVar d-pred)]
      [`(+ ,lhs ,rhs) (PPlus (parse-pred lhs) (parse-pred rhs))]
      [`(- ,lhs ,rhs) (PMinus (parse-pred lhs) (parse-pred rhs))]
      [`(* ,lhs ,rhs) (PMult (parse-pred lhs) (parse-pred rhs))]
      [`(= ,lhs ,rhs) (PNumEq (parse-pred lhs) (parse-pred rhs))] ;; var to the left of =
      [`(and ,lhs ,rhs) (PAnd (parse-pred lhs) (parse-pred rhs))]
      [`(or ,lhs ,rhs) (POr (parse-pred lhs) (parse-pred rhs))]
      [`(not ,bl) (PNot (parse-pred bl))]
      [`(> ,lhs ,rhs) (PGreaterThan (parse-pred lhs) (parse-pred rhs))])))


;; test
(define h (define-types->hash
            '((: a (-> Int Int)) (: b (-> Int Int)) (: c (-> Int Int)) (: c (-> Bool Bool)))))

(make-hash h)