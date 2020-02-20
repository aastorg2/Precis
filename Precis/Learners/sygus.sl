( set-logic BV )

 (synth-fun   p_0_cond1  () Bool ) 
 (synth-fun   p_0_cond2  () Bool ) 
 (synth-fun   p_0_x>3  () Bool ) 
 (synth-fun   p_0_x>=1  () Bool ) 
 (synth-fun   p_0_eq1  () Bool ) 
 (synth-fun   p_0_eq2  () Bool ) 
 (synth-fun   p_0_eq3  () Bool ) 
 (synth-fun   p_1_cond1  () Bool ) 
 (synth-fun   p_1_cond2  () Bool ) 
 (synth-fun   p_1_x>3  () Bool ) 
 (synth-fun   p_1_x>=1  () Bool ) 
 (synth-fun   p_1_eq1  () Bool ) 
 (synth-fun   p_1_eq2  () Bool ) 
 (synth-fun   p_1_eq3  () Bool ) 

 (synth-fun   w_cond1   () Bool) 
 (synth-fun   w_cond2   () Bool) 
 (synth-fun   w_x>3   () Bool) 
 (synth-fun   w_x>=1   () Bool) 
 (synth-fun   w_eq1   () Bool) 
 (synth-fun   w_eq2   () Bool) 
 (synth-fun   w_eq3   () Bool) 
(define-fun cdt (( cond1 Bool) ( cond2 Bool) ( x>3 Bool) ( x>=1 Bool) ( eq1 Bool) ( eq2 Bool) ( eq3 Bool)) Bool 
 (and cond1 x>3)
)

 (declare-const   u_cond1   Bool) 
 (declare-const   u_cond2   Bool) 
 (declare-const   u_x>3   Bool) 
 (declare-const   u_x>=1   Bool) 
 (declare-const   u_eq1   Bool) 
 (declare-const   u_eq2   Bool) 
 (declare-const   u_eq3   Bool) 
(define-fun selectme (( value_0 Bool) ( value_1 Bool) ( value_2 Bool) ( value_3 Bool) ( value_4 Bool) ( value_5 Bool) ( value_6 Bool) ( p_i_0 Bool) ( p_i_1 Bool) ( p_i_2 Bool) ( p_i_3 Bool) ( p_i_4 Bool) ( p_i_5 Bool) ( p_i_6 Bool)) Bool
(ite  p_i_0 value_0
(ite  p_i_1 value_1
(ite  p_i_2 value_2
(ite  p_i_3 value_3
(ite  p_i_4 value_4
(ite  p_i_5 value_5
(ite  p_i_6 value_6
false )))))))
)


(define-fun eval (( cond1 Bool) ( cond2 Bool) ( x>3 Bool) ( x>=1 Bool) ( eq1 Bool) ( eq2 Bool) ( eq3 Bool)) Bool
(ite
(selectme  cond1 cond2 x>3 x>=1 eq1 eq2 eq3 p_0_cond1 p_0_cond2 p_0_x>3 p_0_x>=1 p_0_eq1 p_0_eq2 p_0_eq3 )

(ite
(selectme  cond1 cond2 x>3 x>=1 eq1 eq2 eq3 p_1_cond1 p_1_cond2 p_1_x>3 p_1_x>=1 p_1_eq1 p_1_eq2 p_1_eq3 )

(and 
(=> (not cond1 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   true  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   true  )) 
)
)
(=> (not cond2 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   false  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   true  )) 
)
)
(=> (not x>3 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   true  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   true  )) 
)
)
(=> (not x>=1 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   true  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   true  )) 
)
)
(=> (not eq1 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   true  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   false  )) 
)
)
(=> (not eq2 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   false  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   false  )) 
)
)
(=> (not eq3 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   true  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )     (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )    (not   false  )) 
)
)
)

(and 
(=> (not cond1 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   true  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   true  )) 
)
)
(=> (not cond2 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   false  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   true  )) 
)
)
(=> (not x>3 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   true  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   true  )) 
)
)
(=> (not x>=1 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   true  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   true  )) 
)
)
(=> (not eq1 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   true  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   false  )) 
)
)
(=> (not eq2 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   false  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   false  )) 
)
)
(=> (not eq3 )
(or
 (and       (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  false  true  true  true  false  true  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   true  )) 
 (and       (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )    (not    (selectme  true  true  true  true  false  false  false  p_1_cond1  p_1_cond2  p_1_x>3  p_1_x>=1  p_1_eq1  p_1_eq2  p_1_eq3 )   )   (not   false  )) 
)
)
)
)

(and 
(=> (not cond1 )
(or
 (and     (not    (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   true  )) 
 (and     (not    (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   true  )) 
)
)
(=> (not cond2 )
(or
 (and     (not    (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   false  )) 
 (and     (not    (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   true  )) 
)
)
(=> (not x>3 )
(or
 (and     (not    (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   true  )) 
 (and     (not    (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   true  )) 
)
)
(=> (not x>=1 )
(or
 (and     (not    (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   true  )) 
 (and     (not    (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   true  )) 
)
)
(=> (not eq1 )
(or
 (and     (not    (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   true  )) 
 (and     (not    (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   false  )) 
)
)
(=> (not eq2 )
(or
 (and     (not    (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   false  )) 
 (and     (not    (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   false  )) 
)
)
(=> (not eq3 )
(or
 (and     (not    (selectme  true  false  true  true  true  false  true  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   true  )) 
 (and     (not    (selectme  true  true  true  true  false  false  false  p_0_cond1  p_0_cond2  p_0_x>3  p_0_x>=1  p_0_eq1  p_0_eq2  p_0_eq3 )   )   (not   false  )) 
)
)
)
)

)

(constraint 
(and
(or p_0_cond1 p_0_cond2 p_0_x>3 p_0_x>=1 p_0_eq1 p_0_eq2 p_0_eq3)
(=> p_0_cond1 (and ( not p_0_cond2) ( not p_0_x>3) ( not p_0_x>=1) ( not p_0_eq1) ( not p_0_eq2) ( not p_0_eq3)))
(=> p_0_cond2 (and ( not p_0_cond1) ( not p_0_x>3) ( not p_0_x>=1) ( not p_0_eq1) ( not p_0_eq2) ( not p_0_eq3)))
(=> p_0_x>3 (and ( not p_0_cond1) ( not p_0_cond2) ( not p_0_x>=1) ( not p_0_eq1) ( not p_0_eq2) ( not p_0_eq3)))
(=> p_0_x>=1 (and ( not p_0_cond1) ( not p_0_cond2) ( not p_0_x>3) ( not p_0_eq1) ( not p_0_eq2) ( not p_0_eq3)))
(=> p_0_eq1 (and ( not p_0_cond1) ( not p_0_cond2) ( not p_0_x>3) ( not p_0_x>=1) ( not p_0_eq2) ( not p_0_eq3)))
(=> p_0_eq2 (and ( not p_0_cond1) ( not p_0_cond2) ( not p_0_x>3) ( not p_0_x>=1) ( not p_0_eq1) ( not p_0_eq3)))
(=> p_0_eq3 (and ( not p_0_cond1) ( not p_0_cond2) ( not p_0_x>3) ( not p_0_x>=1) ( not p_0_eq1) ( not p_0_eq2)))
(or p_1_cond1 p_1_cond2 p_1_x>3 p_1_x>=1 p_1_eq1 p_1_eq2 p_1_eq3)
(=> p_1_cond1 (and ( not p_1_cond2) ( not p_1_x>3) ( not p_1_x>=1) ( not p_1_eq1) ( not p_1_eq2) ( not p_1_eq3)))
(=> p_1_cond2 (and ( not p_1_cond1) ( not p_1_x>3) ( not p_1_x>=1) ( not p_1_eq1) ( not p_1_eq2) ( not p_1_eq3)))
(=> p_1_x>3 (and ( not p_1_cond1) ( not p_1_cond2) ( not p_1_x>=1) ( not p_1_eq1) ( not p_1_eq2) ( not p_1_eq3)))
(=> p_1_x>=1 (and ( not p_1_cond1) ( not p_1_cond2) ( not p_1_x>3) ( not p_1_eq1) ( not p_1_eq2) ( not p_1_eq3)))
(=> p_1_eq1 (and ( not p_1_cond1) ( not p_1_cond2) ( not p_1_x>3) ( not p_1_x>=1) ( not p_1_eq2) ( not p_1_eq3)))
(=> p_1_eq2 (and ( not p_1_cond1) ( not p_1_cond2) ( not p_1_x>3) ( not p_1_x>=1) ( not p_1_eq1) ( not p_1_eq3)))
(=> p_1_eq3 (and ( not p_1_cond1) ( not p_1_cond2) ( not p_1_x>3) ( not p_1_x>=1) ( not p_1_eq1) ( not p_1_eq2)))
( => ( eval u_cond1 u_cond2 u_x>3 u_x>=1 u_eq1 u_eq2 u_eq3 ) (cdt u_cond1 u_cond2 u_x>3 u_x>=1 u_eq1 u_eq2 u_eq3))
(cdt w_cond1 w_cond2 w_x>3 w_x>=1 w_eq1 w_eq2 w_eq3)
(not (eval w_cond1 w_cond2 w_x>3 w_x>=1 w_eq1 w_eq2 w_eq3 ))
(=>  p_0_cond1 (and true  (not p_1_cond1 )) )
(=>  p_1_cond1 (and true  (not p_0_cond1 )) )
(=>  p_0_cond2 (and true  (not p_1_cond2 )) )
(=>  p_1_cond2 (and true  (not p_0_cond2 )) )
(=>  p_0_x>3 (and true  (not p_1_x>3 )) )
(=>  p_1_x>3 (and true  (not p_0_x>3 )) )
(=>  p_0_x>=1 (and true  (not p_1_x>=1 )) )
(=>  p_1_x>=1 (and true  (not p_0_x>=1 )) )
(=>  p_0_eq1 (and true  (not p_1_eq1 )) )
(=>  p_1_eq1 (and true  (not p_0_eq1 )) )
(=>  p_0_eq2 (and true  (not p_1_eq2 )) )
(=>  p_1_eq2 (and true  (not p_0_eq2 )) )
(=>  p_0_eq3 (and true  (not p_1_eq3 )) )
(=>  p_1_eq3 (and true  (not p_0_eq3 )) )
))
(check-synth)