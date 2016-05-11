#lang racket

(provide (all-defined-out))

(struct Let (var val body) #:transparent)
(struct Letrec (var val body) #:transparent)
(struct LetK (var body env addr) #:transparent)
(struct EndK (label arg addr) #:transparent)
(struct Greater (l s) #:transparent)
(struct State (exp env kont time) #:transparent)
;(struct State (exp env store kont time) #:transparent)

; Exp
(struct Var (name) #:transparent)
(struct Lam (label var exp) #:transparent)
(struct App (fun arg) #:transparent)
(struct Int (pred) #:transparent)
(struct Bool (pred) #:transparent)
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

; Type
(struct DefineType (name type) #:transparent)
(struct TAny () #:transparent)
(struct TUnit () #:transparent)
(struct TArrow (arg ret) #:transparent)
(struct TIs (arrows) #:transparent)

; Predicate
(struct PVar (name) #:transparent)
(struct PSelf () #:transparent)
(struct PGreater (l r) #:transparent)
(struct PAnd (l r) #:transparent)
(struct POr (l r) #:transparent)
(struct PNot (b) #:transparent)

(struct PInt (pred) #:transparent)
(struct PPlus (l r) #:transparent)
(struct PMinus (l r) #:transparent)
(struct PMult (l r) #:transparent)
(struct PNumEq (l r) #:transparent)

;;;;;;;;;;;;;;;;;;

; Continuation
(struct DoneK () #:transparent)
(struct ArgK (exp env addr) #:transparent)
(struct AppK (lam env addr) #:transparent)
(struct PlusK (r env addr) #:transparent)
(struct DoPlusK (l addr) #:transparent)
(struct MinusK (r env addr) #:transparent)
(struct DoMinusK (l addr) #:transparent)
(struct MultK (r env addr) #:transparent)
(struct DoMultK (l addr) #:transparent)
(struct AndK (r env addr) #:transparent)
(struct DoAndK (l addr) #:transparent)
(struct OrK (r env addr) #:transparent)
(struct DoOrK (l addr) #:transparent)
(struct DoNotK (addr) #:transparent)
(struct DoIfK (thn els env addr) #:transparent)
(struct SetK (var addr) #:transparent)
(struct BeginK (s2 addr) #:transparent)
(struct NumEqK (r env addr) #:transparent)
(struct DoNumEqK (l addr) #:transparent)

; Storable / Value
(struct Clo (lam env) #:transparent)
(struct Cont (k) #:transparent)
(struct IntValue (pred) #:transparent)
(struct BoolValue (pred) #:transparent)
(struct VoidValue () #:transparent)

(struct True () #:transparent)
(struct False () #:transparent)

; Address
(struct BAddr (var time) #:transparent)
(struct KAddr (exp time) #:transparent)