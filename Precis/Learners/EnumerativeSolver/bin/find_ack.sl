(set-logic LIA)



(synth-fun find ((r Bool)(a1 Bool)(a2 Bool)(a3 Bool)) Bool
     (
        (Start Bool ( true false
                      a1 a2 a3 r
                      ;(ite Start Start Start) 
                      (and Start Start)
                      (or  Start Start)
                      (not Start)

                    )
        )
        
      )
)

(define-fun and34 ((a1 Bool)(a2 Bool)(a3 Bool)(a4 Bool)(a5 Bool)(a6 Bool)(a7 Bool)(a8 Bool)(a9 Bool)(a10 Bool)(a11 Bool)(a12 Bool)(a13 Bool)(a14 Bool)(a15 Bool)(a16 Bool)(a17 Bool)(a18 Bool)(a19 Bool)(a20 Bool)(a21 Bool)(a22 Bool)(a23 Bool)(a24 Bool)(a25 Bool)(a26 Bool)(a27 Bool)(a28 Bool)(a29 Bool)(a30 Bool)(a31 Bool)(a32 Bool)(a33 Bool)(a34 Bool)) Bool
( and a1 ( and a2 (and a3  (and a4  (and a5  (and a6  (and a7  (and a8 (and a9  (and a10  (and a11  (and a12  (and a13  (and a14  (and a15  (and a16  (and a17  (and a18  (and a19  (and a20  (and a21  (and a22  (and a23  (and a24  (and a25  (and a26  (and a27  (and a28  (and a29  (and a30  (and a31  (and a32  (and a33   a34 )))))))))))))))))))))))))))))))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-var  r Bool)
(declare-var  l Int)
(declare-var  e Int)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-var next_l Int)
(declare-var next_next_l Int)

(declare-var data_l Int)
(declare-var data_next_l Int)

(declare-var Union_Sing_data_l__S_next_l Int)
(declare-var Union_Sing_data_next_l__S_next_next_l Int)

(declare-var Sing_data_next_l Int)
(declare-var Sing_data_l Int)

(declare-var list_l Bool)
(declare-var list_next_l Bool)
(declare-var list_next_next_l Bool)

(declare-var Emp Int)


(declare-var S_l  Int ) 
(declare-var S_next_l  Int )
(declare-var S_next_next_l  Int )




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-var ElementOf_Emp__e  Bool ) 
(declare-var ElementOf_S_l__e   Bool ) 
(declare-var ElementOf_S_next_l__e   Bool ) 
(declare-var ElementOf_S_next_next_l__e  Bool ) 
(declare-var ElementOf_Union_Sing_data_l__S_next_l__e   Bool ) 
(declare-var ElementOf_Union_Sing_data_next_l__S_next_next_l__e   Bool ) 




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;find-function 
;(define-fun find ((l List )(e Int) (r Bool)) Bool
;   (ite (= l 0 ) 
;        false 
;        (ite (=  data_l e ) true  r  )
;     )
;)


;(define-fun find ( (r Bool) ( a1 Bool)( a2 Bool)( a3 Bool)) Bool
;   ( and ( not a1 ) ( or r a3  ) )
;)



( constraint 
  (=>  
    (and34 

    	( => 
            ( = l next_l )
            ( = S_l S_next_l )
         )


		(= ElementOf_Union_Sing_data_next_l__S_next_next_l__e 
                 
            (or (= e data_next_l) 
                 ElementOf_S_next_next_l__e  
            ) 
        )


	(= ElementOf_Union_Sing_data_l__S_next_l__e  
        
      (or 
        (= e data_l) 
        ElementOf_S_next_l__e 
          
      ) 
    )		


	(= ElementOf_Emp__e  
             false 
         )



(= S_next_l  
       (ite (= next_l 0 )  
          Emp 
          Union_Sing_data_next_l__S_next_next_l 
        ) 
     )


(= S_l  
      (ite (= l 0 )  
          Emp 
          Union_Sing_data_l__S_next_l 
      ) 
    ) 


(= list_next_l  
      (or (=  next_l 0 ) 
         list_next_next_l  
      )
    )



(= list_l  
      (or (= l 0)  
         list_next_l 
      )
    )


( => 
            ( =  l  next_next_l )
            (= list_l list_next_next_l )
         )



( => 
            ( =  next_l   next_next_l )
            (= list_next_l list_next_next_l )
         )



         ( => 
            ( = l next_l )
            (= list_l list_next_l )
         )


( => 
            ( = data_next_l  data_l )
            (= Sing_data_next_l Sing_data_l )
         )


( => 
            ( and ( = Sing_data_l  Sing_data_next_l )  ( =  S_next_l  S_next_next_l ) )
            (= Union_Sing_data_l__S_next_l  Union_Sing_data_next_l__S_next_next_l )
         )


( => 
            ( = l next_l )
            (= data_l data_next_l )
         )


( => 
            ( = l next_l )
            (= next_l next_next_l )
         )

( => 
            ( = Union_Sing_data_l__S_next_l Union_Sing_data_next_l__S_next_next_l ) 
            (= ElementOf_Union_Sing_data_l__S_next_l__e 
               ElementOf_Union_Sing_data_next_l__S_next_next_l__e 
            )
)


( => 
            ( = l next_next_l )
            ( = S_l S_next_next_l )
         )


( => 
            ( = next_l next_next_l )
            ( = S_next_l S_next_next_l )
         )



( => 
            ( = Emp S_l )
            (= ElementOf_Emp__e 
               ElementOf_S_l__e 
            )
)


( => 
            ( = Emp S_next_l  )
            (= ElementOf_Emp__e 
               ElementOf_S_next_l__e 
            )
)


( => 
            ( = Emp S_next_next_l ) 
            (= ElementOf_Emp__e 
               ElementOf_S_next_next_l__e 
            )
)


( => 
            ( = Emp Union_Sing_data_l__S_next_l ) 
            (= ElementOf_Emp__e 
               ElementOf_Union_Sing_data_l__S_next_l__e 
            )
)



( => 
            ( = Emp Union_Sing_data_next_l__S_next_next_l ) 
            (= ElementOf_Emp__e 
               ElementOf_Union_Sing_data_next_l__S_next_next_l__e 
            )
)



( => 
            ( = S_l S_next_l  )
            (= ElementOf_S_l__e 
               ElementOf_S_next_l__e 
            )
)


( => 
            ( = S_l S_next_next_l ) 
            (= ElementOf_S_l__e 
               ElementOf_S_next_next_l__e 
            )
)


( => 
            ( = S_l Union_Sing_data_l__S_next_l ) 
            (= ElementOf_S_l__e 
               ElementOf_Union_Sing_data_l__S_next_l__e 
            )
)



( => 
            ( = S_l Union_Sing_data_next_l__S_next_next_l ) 
            (= ElementOf_S_l__e 
               ElementOf_Union_Sing_data_next_l__S_next_next_l__e 
            )
)


( => 
            ( = S_next_l S_next_next_l ) 
            (= ElementOf_S_next_l__e 
               ElementOf_S_next_next_l__e 
            )
)


( => 
            ( = S_next_l Union_Sing_data_l__S_next_l ) 
            (= ElementOf_S_next_l__e 
               ElementOf_Union_Sing_data_l__S_next_l__e 
            )
)


( => 
            ( = S_next_l Union_Sing_data_next_l__S_next_next_l ) 
            (= ElementOf_S_next_l__e 
               ElementOf_Union_Sing_data_next_l__S_next_next_l__e 
            )
)


( => 
            ( = S_next_next_l Union_Sing_data_l__S_next_l ) 
            (= ElementOf_S_next_next_l__e 
               ElementOf_Union_Sing_data_l__S_next_l__e 
            )
)

( => 
            ( = S_next_next_l Union_Sing_data_next_l__S_next_next_l ) 
            (= ElementOf_S_next_next_l__e 
               ElementOf_Union_Sing_data_next_l__S_next_next_l__e 
            )
)


    	list_l 
        (=>  list_next_l 
          (= r  ElementOf_S_next_l__e  )
        )
    )

      (=  ElementOf_S_l__e  
        (find r ( = l 0 ) ( =  next_l 0 ) ( =  data_l e ) )
      ) 

  )
)
 

(check-synth)
