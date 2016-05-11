#lang racket

(require "anf.rkt")
(require "structs.rkt")
(require "parsers.rkt")

; Example 1-1
; id should be (Int -> Int), but user provide (Int -> Bool)
(define wrong-contract (define-types->hash '((: id (-> Int Bool)))))

(define id (parse '{lambda id {x} x}))

(verify-contract id wrong-contract) ;reject

;============================================

; Example2: check runtime type without predicate
; id: int -> int
(define contract2 (define-types->hash '((: id (-> Int Int)))))

; id could has an intersection type (int -> int) & (bool -> bool)
(define contract2-bool (define-types->hash '((: id (-> Int Int))
                                             (: id (-> Bool Bool)))))

(define example2 (parse '{let {{id {lambda id {x} x}}}
                           {let {{one {id 1}}}
                             {let {{fls {id false}}}
                               one}}}))

(verify-runtime example2 contract2)       ; reject
(verify-runtime example2 contract2-bool)  ; accept

;============================================

; Example3: higher-order function and contract with predicate
; add1: int[x>0] -> int[y>1]
; add2: int[x>3 && x<9] -> int[x>5 && x<11]
(define contract3 (define-types->hash
                    '((: add1 (-> (Int (> _ 0)) (Int (> _ 1))))
                      (: add2 (-> (Int (and (> _ 3) (< _ 9)))
                                  (Int (and (> _ 5) (< _ 11))))))))

(define example3 (parse '{let {{add1 {lambda add1 {x} {+ 1 x}}}}
                           {let {{add2 {lambda add2 {x} {+ 2 x}}}}
                             {let {{apply {lambda applyf {f} {lambda applyg {g} {f g}}}}}
                               {let {{another_add1 {apply add1}}}
                                 {let {{another_add2 {apply add2}}}
                                   {let {{two {another_add1 1}}}
                                     {let {{three {another_add1 two}}}
                                       {another_add2 2}}}}}}}}))

; reject becuase {another_add2 2} does not satisfy precondition of add2
(verify-runtime example3 contract3)


;============================================

; Example4: higher-order function and contract with predicate
; multiple5: int[x>3] -> int[y>15]
; multiple7: int[x>1 && x<3] -> int[x>7 && x<21]
(define contract4 (define-types->hash
                    '((: multiple5 (-> (Int (> _ 3)) (Int (> _ 15))))
                      (: multiple7 (-> (Int (and (> _ 1) (< _ 3)))
                                  (Int (and (> _ 7) (< _ 21))))))))

(define example4 (parse '{let {{multiple5 {lambda multiple5 {x} {* 5 x}}}}
                           {let {{multiple7 {lambda multiple7 {x} {* 7 x}}}}
                             {let {{apply {lambda applyf {f} {lambda applyg {g} {f g}}}}}
                               {let {{another_multiple5 {apply multiple5}}}
                                 {let {{another_multiple7 {apply multiple7}}}
                                   {let {{twenty {another_multiple5 4}}}
                                     {let {{a-hundred-forty {another_multiple7 twenty}}}
                                       {another_multiple7 2}}}}}}}}))

; reject becuase {another_add2 2} does not satisfy precondition of add2
(verify-runtime example4 contract4)

;============================================

; Example5: check contract with bool
; forever-true: bool -> bool[true]
(define contract5 (define-types->hash
                    '((: forever-true (-> Bool (Bool true))))))

(define forever-true (parse '{lambda forever-true {b} true}))

; accept
(verify-contract forever-true contract5)