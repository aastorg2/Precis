(set-logic LIA)

(synth-fun max3 ((x Int) (y Int) (z Int)) Int
    ((Start Int (x
                 y
                 z
                 (+ Start Start)
                 (- Start Start)
                 (ite StartBool Start Start)))
     (StartBool Bool ((and StartBool StartBool)
                      (or  StartBool StartBool)
                      (not StartBool)
                      (<=  Start Start)
                      (=   Start Start)
                      (>=  Start Start)))))



(declare-var x Int)
(declare-var y Int)
(declare-var z Int)


(constraint ( = ( max3  5 3 6) 6 ))
(constraint ( = ( max3  9 3 1) 9 ))
(constraint ( = ( max3  1 7 4) 7 ))
(constraint ( = ( max3  7 4 6) 7 ))
(constraint ( = ( max3  1 4 5) 5 ))
(constraint ( = ( max3  8 5 7) 8 ))

(check-synth)
