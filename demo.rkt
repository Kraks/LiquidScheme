#lang racket

(require "parsers.rkt")
(require "anf.rkt")
(require "structs.rkt")

; Example1: type checking without predicate
; id :: int -> int
(define contract1 (hash 'id (set (TArrow (IntValue #t) (IntValue #t)))))

(define example1 (parse '{let {{id {lambda id {x} x}}}
                           {let {{one {id 1}}}
                             {let {{fls {id false}}}
                               one}}}))

(verify-contract example1 contract1)

; Example2: higher-order function
; add1: int[x>0] -> int[y>1]
; add2: int[x>3 && x<9] -> int[x>5 && x<11]
(define contract2 (hash 'add1 (set (TArrow (set (IntValue (PGreater (PSelf) 0)))
                                           (set (IntValue (PGreater (PSelf) 1)))))
                        'add2 (set (TArrow (set (IntValue (PAnd (PGreater (PSelf) 3)
                                                                (PGreater 9 (PSelf)))))
                                           (set (IntValue (PAnd (PGreater (PSelf) 5)
                                                                (PGreater 11 (PSelf)))))))))
(define example2 (parse '{let {{add1 {lambda add1 {x} {+ 1 x}}}}
                           {let {{add2 {lambda add2 {x} {+ 2 x}}}}
                             {let {{apply {lambda applyf {f} {lambda applyg {g} {f g}}}}}
                               {let {{another_add1 {apply add1}}}
                                 {let {{another_add2 {apply add2}}}
                                   {let {{two {another_add1 1}}}
                                     {let {{three {another_add1 two}}}
                                       {another_add2 1}}}}}}}}))