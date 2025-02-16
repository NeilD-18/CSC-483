;Start every SMTLIB file with
(set-logic ALL)
;Turn on the option to get counter-models if necessary
(set-option :produce-models true)

;Declare all your variables

; a (5 bits), b (5 bits) 
(declare-const a0 Bool)
(declare-const a1 Bool)
(declare-const a2 Bool)
(declare-const a3 Bool)
(declare-const a4 Bool)

(declare-const b0 Bool)
(declare-const b1 Bool)
(declare-const b2 Bool)
(declare-const b3 Bool)
(declare-const b4 Bool)

;result d (5bits)
(declare-const d0 Bool)
(declare-const d1 Bool)
(declare-const d2 Bool)
(declare-const d3 Bool)
(declare-const d4 Bool)


;carry c (5 bits)
(declare-const c0 Bool)
(declare-const c1 Bool)
(declare-const c2 Bool)
(declare-const c3 Bool)
(declare-const c4 Bool)
(declare-const c5 Bool)


;inputs
(assert (and (not a4) (not a3) a2 a1 a0))
(assert (and (not b4) b3 b2 (not b1) b0))

;addition logic

; Full adder logic for each bit
(assert (= d0 (xor a0 b0 c0)))
(assert (= d1 (xor a1 b1 c1)))
(assert (= d2 (xor a2 b2 c2)))
(assert (= d3 (xor a3 b3 c3)))
(assert (= d4 (xor a4 b4 c4)))


(assert (= c1 (or (and a0 b0) (and a0 c0) (and b0 c0))))
(assert (= c2 (or (and a1 b1) (and a1 c1) (and b1 c1))))
(assert (= c3 (or (and a2 b2) (and a2 c2) (and b2 c2))))
(assert (= c4 (or (and a3 b3) (and a3 c3) (and b3 c3))))
(assert (= c5 (or (and a4 b4) (and a4 c4) (and b4 c4))))

(assert (not c0))
(assert (not c5))

;Type can be Bool


;End file with
(check-sat)
;for checking satisfiability

;Add this command if you want counter-models:
(get-model)
 