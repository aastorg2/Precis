(set-logic LIA)
                ( synth-fun Precondition ( (VariableInt000 Int) (VariableInt001 Int) (VariableInt002 Int) (VariableBool000 Bool) (VariableBool001 Bool) ) Bool (
                        ( Start Bool (StartBool) )
                                ( StartBool Bool (
                                        true false
                                        VariableBool000 VariableBool001
                                                (and StartBool StartBool)
                                                (and StartBool StartBool)
                                                (not StartBool)
                                                (<=  StartInt StartInt)
                                                (= StartInt StartInt)
                                                (>=  StartInt StartInt)
                                ) )
                                ( StartInt Int (
                                        0 1
                                        VariableInt000 VariableInt001 VariableInt002
                                                (+ StartInt StartInt)
                                                (- StartInt StartInt)
                                                (ite StartBool StartInt StartInt)
                                ) )
                ) )
                
                
                ; (declare-var VariableInt000 Int) 
                ; (declare-var VariableInt001 Int) 
                ; (declare-var VariableInt002 Int) 
                ; (declare-var VariableBool000 Bool) 
                ; (declare-var VariableBool001 Bool)
                
                
                ; (define-fun implies ((b1 Bool) (b2 Bool)) Bool (or (not b1) b2))
                ; (define-fun and3 ((b1 Bool) (b2 Bool) (b3 Bool)) Bool (and (and b1 b2) b3))
                ; (define-fun and4 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool)) Bool (and (and3 b1 b2 b3) b4))
                ; (define-fun and5 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool) (b5 Bool)) Bool (and (and4 b1 b2 b3 b4) b5))
                ; (define-fun and6 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool) (b5 Bool) (b6 Bool)) Bool (and (and5 b1 b2 b3 b4 b5) b6))
                ; (define-fun or3 ((b1 Bool) (b2 Bool) (b3 Bool)) Bool (or (or b1 b2) b3))
                ; (define-fun or4 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool)) Bool (or (or3 b1 b2 b3) b4))
                ; (define-fun or5 ((b1 Bool) (b2 Bool) (b3 Bool) (b4 Bool) (b5 Bool)) Bool (or (or4 b1 b2 b3 b4) b5))

                                
                                
                ; (constraint ( implies 
                ;                 (and5 
                ;                         (= VariableInt000 1) 
                ;                         (= VariableInt001 1)
                ;                         (= VariableInt002 0)
                ;                         VariableBool000
                ;                         VariableBool001
                ;                 )
                ;                ( Precondition      VariableInt000   VariableInt001  VariableInt002   VariableBool000  VariableBool001 ) 
                ;         )
                ; )
                
                
                ; (constraint ( implies 
                ;                 (and5 
                ;                         (= VariableInt000 2) 
                ;                         (= VariableInt001 1)
                ;                         (= VariableInt002 0)
                ;                         (not VariableBool000)
                ;                         VariableBool001
                ;                 )
                ;                ( not ( Precondition      VariableInt000   VariableInt001  VariableInt002   VariableBool000  VariableBool001 ) )
                ;         )
                ; )
                
                
                (constraint ( Precondition 1 1 0 true true ) )
                (constraint ( not ( Precondition 2 1 0 false true ) ) )
                ( constraint ( not ( Precondition 1 1 0 false true ) ) )
                ( constraint ( not ( Precondition 2 0 0 true true ) ) )
                ( constraint ( Precondition 1 0 0 true true ) )
                ( constraint ( not ( Precondition 0 2 2 false false ) ) )
                
                
                
                ; ( constraint ( not ( Precondition 0 2 0 false false ) ) )
                ; ( constraint ( Precondition 0 0 0 false false ) )
                ; ( constraint ( not ( Precondition 2 0 1 true false ) ) )
                ; ( constraint ( Precondition 0 2 2 false false ) )
                ; ( constraint ( not ( Precondition 2 0 0 true true ) ) )
                ; ( constraint ( not ( Precondition 1 0 0 true true ) ) )
                
                
                
                
                ; ( constraint ( not ( Precondition 0 2147483647 0 false false ) ) )

                ; ( constraint ( not ( Precondition 0 -2147483647 -2147483648 false false ) ) )
(check-synth)
