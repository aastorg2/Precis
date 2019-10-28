(set-logic LIA)

(synth-inv inv_fun ((x Int)))

(declare-primed-var x Int)

(define-fun pre_fun ((x Int)) Bool
    (or 
        ( > x 99 )
        ( = x 2)
    )
)


(define-fun trans_fun ((x Int) (x! Int)) Bool
    (and  (= x x!) )
)

(define-fun post_fun ((x Int)) Bool
    (and 
        ;( = x 1)
        (not ( = x 99))
        (not ( <= x 1))
    )
)

(inv-constraint inv_fun pre_fun trans_fun post_fun)

(check-synth)



; https://www.wolframalpha.com/input/?i=simplify(+P+%3D%3E+1+)
; a => true   = true
; a => false  = not a
; true => a   = a
; false => a  = true   


; (constraint (=> (pre-f x y b)
;                 (inv-f x y b)))

; (constraint (=> (and (inv-f x y b) (trans-f x y b x! y! b!))
;                 (inv-f x! y! b!)))

; (constraint (=> (inv-f x y b)
;                 (post-f x y b)))





; (set-logic LIA)

; (synth-inv inv_fun ((x Int)))

; (declare-primed-var x Int)

; (define-fun pre_fun ((x Int)) Bool
;     (= x 0)
; )


; (define-fun trans_fun ((x Int) (x! Int)) Bool
;     (and (< x 100) (= x! (+ x 1)))
; )

; (define-fun post_fun ((x Int)) Bool
;     (or (not (>= x 100)) (= x 100))
; )

; (inv-constraint inv_fun pre_fun trans_fun post_fun)

; (check-synth)

