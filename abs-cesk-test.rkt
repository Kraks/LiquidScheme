#lang racket

(require "abs-cesk.rkt")
(require "parsers.rkt")

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

;(define s13 (aval (parse '{if {= 1 2} 2 3})))

(define fact1 (parse '{let {{fact {void}}}
                       {begin {set! fact {lambda fact {n} {if {= n 0}
                                                              1
                                                              {* n {fact {- n 1}}}}}}
                              {fact 5}}}))
;(aval-infer fact1)

(define fact2 (parse '{letrec {{fact {lambda fact {n} {if {= n 0}
                                                          1
                                                          {* {fact {- n 1}} n}}}}}
                        {fact 5}}))
;(aval-infer fact2)

(define tozero (parse '{letrec {{tozero {lambda tozero {n} {if {= n 0} false
                                                               {if {= n 1} 1
                                                                   {tozero {- n 1}}}}}}}
                         {tozero 5}}))
;(aval-infer tozero)

(define toten (parse '{letrec {{toten {λ toten {n} {if {= n 10} false
                                                       {toten {+ n 1}}}}}}
                        {toten 1}}))
;(aval-infer toten)

(define fib (parse '{letrec {{fib {lambda fib {n} {if {= n 1}
                                                      1
                                                      {+ {fib {- n 1}} {fib {- n 2}}}}}}}
                      {fib 5}}))
;(aval-infer fib)

(define idid (parse '{{lambda {x} x} {lambda {y} y}}))
;(aval-infer idid)

; If using 0-CFA, this test case will get wrong.
#;
(aval-infer (parse '{let {[id {lambda id {x} x}]}
                      {let {[one {id 1}]}
                        {let {[fls {not {id true}}]}
                          fls}}}))