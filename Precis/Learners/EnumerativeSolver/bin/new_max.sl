(set-logic LIA)

(synth-fun max2 ((x Bool) (y Bool)) Bool
    (
        (Start  Bool (StartBool)) 
         (StartBool  Bool 
                    (   true
                        false
                        (and StartBool StartBool)
                        (or  StartBool StartBool)
                        (not StartBool)
                    ; for integers    
                        ; (<=  StartInt StartInt) ; 
                        ; (=   StartInt StartInt) ; ??
                        ; (>=  StartInt StartInt) ; ??

                    )
        )
        
        ; (StartInt   Int 
        ;             (
        ;                 x ;int variables
        ;                 y ;int variables
                        
        ;                 0 ; Constants ??? 
        ;                 1
                        
        ;                 (+ StartInt StartInt)
        ;                 (- StartInt StartInt)
        ;                 (ite StartBool StartInt StartInt)
        ;             )
        ; )
       
    )
)

; Do we need universal variables 
; x = ? and y = ? => max(x,y)
; max(2,3,)


(declare-var x Bool)
(declare-var y Bool)

(constraint (max2 true true))
(constraint (not (max2 true false)))

; (constraint 
; (constraint (or (= x (max2 x y))
; 				(= y (max2 x y))))


(check-synth)





; GRAMMAR: ORIGINAL PARSED
; ----------------------------------
; (synth-fun max2 ((x Int) (y Int)) Int
;     (
;         (Start Int (
;                     x
;                     y
;                     0
;                     1
;                     (+ Start Start)
;                     (- Start Start)
;                     (ite StartBool Start Start)
;                     )
;         )
;         (StartBool Bool (
;                         (and StartBool StartBool)
;                         (or  StartBool StartBool)
;                         (not StartBool)
;                         (<=  Start Start)
;                         (=   Start Start)
;                         (>=  Start Start)
;                         )
;         )
;     )
; )



; GRAMMAR MODIFIED: seperate Start
; --------------------------------
; (synth-fun max2 ((x Int) (y Int)) Int
;     (
;         (Start  Int (StartInt)) 
;         (StartInt   Int 
;                     (
;                         x
;                         y
;                         0
;                         1
;                         (+ StartInt StartInt)
;                         (- StartInt StartInt)
;                         (ite StartBool StartInt StartInt)
;                     )
;         )
;         (StartBool  Bool 
;                     (
;                         (and StartBool StartBool)
;                         (or  StartBool StartBool)
;                         (not StartBool)
;                         (<=  StartInt StartInt)
;                         (=   StartInt StartInt)
;                         (>=  StartInt StartInt)
;                     )
;         )
;     )
; )





; (declare-var x Int)
; (declare-var y Int)

; (constraint (>= (max2 x y) x))
; (constraint (>= (max2 x y) y))
; (constraint (or (= x (max2 x y))
; 				(= y (max2 x y))))


; (check-synth)



; A hSynthF unCmdi describes the sort and syntax of a function to be synthesized. The hSynthF unCmdi
; specifies the function name, input parameters, output sort, and grammar production rules respectively. The
; production rules corresponding to each non-terminal are described by an hNT Defi, which specifies, in order,
; the non-terminal name, the sort of the resulting productions, and a non-empty sequence of production rules.
; Each hGT ermi corresponds to a production rule.
