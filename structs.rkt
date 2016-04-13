#lang racket

(struct True () #:transparent)
(struct False () #:transparent)

; Type
(struct DefineType (name type) #:transparent)
(struct TInt (pred) #:transparent)
(struct TBool (pred) #:transparent)
(struct TAny () #:transparent)
(struct TArrow (arg ret) #:transparent)
(struct TIs (arrows) #:transparent)

; Predicate
(struct PSelf () #:transparent)
(struct PVar (name) #:transparent)
(struct PGreater (l r) #:transparent)
(struct PNumEq (l r) #:transparent)
(struct PAnd (l r) #:transparent)
(struct POr (l r) #:transparent)
(struct PNot (b) #:transparent)