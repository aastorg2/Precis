(set-logic LIA)

;declare sort macro
(define-sort MSet Int)
(define-sort List Int)

;(l List)(e Int)

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




;declare main constants
(declare-var  r Bool)
(declare-var  l List)
(declare-var  e Int)

;declare structure members
(declare-fun next (List) List)
(declare-fun data (List) Int)

;declare set operations
(declare-fun Emp () MSet)
(declare-fun Sing (Int) MSet )
(declare-fun Union (MSet MSet) MSet )
(declare-fun ElementOf ( MSet Int) Bool )




;declare list
(declare-fun list ( List) Bool ) 

;list definition
(constraint (= (list l ) 
      (or (= l 0)  
         (list (next l ))
      )
    )
)

(constraint (= (list (next l )) 
      (or (= ( next l) 0 ) 
         (list (next (next l)))  
      )
    )
)

;Pre definition- uses List definition
(define-fun Pre (( l List)) Bool
( list l)
)




;declare sets
(declare-fun S (List) MSet )
 
;set definition
(constraint (= (S l ) 
      (ite (= l 0 )  
          Emp 
          (Union (Sing (data l) ) 
                (S (next l)) 
          )
      ) 
    ) 
)  

(constraint (= (S (next l) ) 
       (ite (= (next l) 0 )  
          Emp 
          (Union 
            (Sing (data (next l)) )   
            (S  (next (next l)) ) 
          ) 
        ) 
     )
)



;elementOf definiton
(constraint (= (ElementOf Emp e ) 
             false 
         )
)

(constraint (= (ElementOf  
        (Union 
          (Sing (data l )) 
          (S (next l))
         )  
         e 
      ) 
      (or 
        (= e (data l)) 
        (ElementOf 
          (S (next l) ) 
          e 
        )  
      ) 
    )
)

(constraint (= (ElementOf 
        (Union  
                      (Sing (data (next l) ))  
                      (S (next (next l) ) ) 
                 ) 
                 e 
            ) 
            (or (= e (data (next l))) 
                 (ElementOf (S (next (next l) )) e )  
            ) 
        )
)

;Post definion - uses S and ElementOf
(define-fun Post ((l List)(e Int)) Bool
  ( ElementOf (S l) e )
)



;attributes
(define-fun a1 () Bool
 ( = l 0 )
)

(define-fun a2 () Bool
 ( = ( next l) 0 )
)


(define-fun a3 () Bool
 ( = ( data l) e )
)



;find-function 
;(define-fun find ((l List )(e Int) (r Bool)) Bool
;   (ite (= l 0 ) 
;       false 
;       (ite (=  (data l ) e ) true  r  )
;    )
;)



;main constraint - uses Pre Post and find
(constraint 
;(not 
  (=>  
    (and (Pre l) 
        (=>  (Pre (next l)) 
          (= r  (Post (next l ) e ) )
        )
    )

      (=  (Post l e ) 
          (find r a1 a2 a3 )
      ) 

  )
;)
)


(check-synth)

