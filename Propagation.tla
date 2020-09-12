-------------------------- MODULE Propagation --------------------------

EXTENDS Integers, TLAPS

CONSTANTS Replicas, Values, Coordinators

\* The following variables together constitute the system state
VARIABLES 
          msgs,    \* The set of messages that have been delivered.
          knowVal,  \* val[x] is true is a replica x knows a value
          allKnowVal, \* allKnowVal[a] is TRUE if replica knows that all 
                       \*other replicas know the value 
          cordVal, \* cordVal[a] value ervery coordinator is trying to propagate             
          safeStateAttained, \* safeStateAttained[x] is true if an agent x knows that
                         \* the required state of knowledge has been attained             
          state_time \* time of the system state
          


(***************************************************************************)
(*Time                                                                     *)
(***************************************************************************)
\* for now, representing time with natural numbers such as t_0, t_1, t_2,...
\* since using no other property but existence and greater than
\* time is discrete logical time
Time == Nat

(***************************************************************************)
(* Some temporal properties                                                *)
(***************************************************************************)
\* If a message has been delivered from all replicas at different times, 
\* there will be a time when the new system state will have that message 
\* from all replicas
temporalProperty1 ==
(
(\A r \in Replicas : \E t \in Time : (state_time' = t) 
                                   /\ (\E m \in msgs' :  (m.rep = r)))
=> (\E T \in Time : state_time' = T 
                /\ (\A r \in Replicas : (\E m \in msgs' : (m.rep = r))))
)

\* For all coordinators, there is a time when no messages have been sent to or from it
temporalProperty2 ==
\A c \in Coordinators: 
(\E t \in Time :   state_time = t
                 /\ (~(\E m \in msgs : m.cord = c)))

\*if some new state X exists at a time t, then X is the current state at some time t2>t
\* the following property includes multiple variations for pattern matching
temporalProperty3 ==
 (
    \A t \in Time:
     \A c \in Coordinators:   
       ((    state_time' = t
             /\ \E v \in Values : 
                  \E m \in msgs' : m.type = "1a" 
                                /\ m.cord = c 
                                /\ m.val = v) 
     =>
      (\E t2 \in Time:
             t2>t
           /\ state_time = t2  
           /\ \E v \in Values : 
                \E m \in msgs : m.type = "1a" 
                              /\ m.cord = c 
                              /\ m.val = v)) 
  )

/\(
    \A t \in Time:
     \A c \in Coordinators:   
          (state_time' = t
           /\ \A r \in Replicas : 
               \E m \in msgs' : m.type = "1b" 
                             /\ m.cord = c 
                             /\ m.rep = r) 
     =>
      (\E t2 \in Time:
             t2>t
           /\ state_time = t2  
           /\ \A r \in Replicas : 
               \E m \in msgs : m.type = "1b" 
                            /\ m.cord = c 
                            /\ m.rep = r) 
  )
  
/\(
    \A t \in Time:
     \A c \in Coordinators:   
          (state_time' = t
           /\ \E m \in msgs' : m.cord = c 
                           /\  m.type = "2a") 
     =>
      (\E t2 \in Time:
             t2>t
           /\ state_time = t2  
           /\ \E m \in msgs : m.cord = c 
                          /\  m.type = "2a") 
  )
  
/\(
    \A t \in Time:
     \A c \in Coordinators:   
          (state_time' = t
           /\ \A r \in Replicas : 
               \E m \in msgs' : m.type = "2b" 
                             /\ m.cord = c 
                             /\ m.rep = r) 
     =>
      (\E t2 \in Time:
             t2>t
           /\ state_time = t2  
           /\ \A r \in Replicas : 
               \E m \in msgs : m.type = "2b" 
                            /\ m.cord = c 
                            /\ m.rep = r) 
  )  
    

temporalProperties == temporalProperty1
                   /\ temporalProperty2
                   /\ temporalProperty3

(***************************************************************************)
(*Predicates for message sending and delivery                              *)
(*                                 NOTE                                    *) 
(*                                                                         *)
(*  A message is added to msgs once delivered                              *)
(*  Only the msgs is accessible by agents                                  *) 
(***************************************************************************)
\*sending a message does not change system state, so using an abstract definiion   
CONSTANT Send(_,_) 


\*A message that is Delivered is added to msgs
\* A single msgs variable implies that if a message is delivered, 
\* it is delivered to all acceptors at the same time, i.e., broadcast 
Deliver(m,t) == (state_time' = t) /\ (msgs' = msgs \cup {m}) 

            
(***************************************************************************)
(* Phase 1a: A coordinator sends a "1a" message to all replicas            *)
(***************************************************************************)
Phase1a(c,t ) ==               
          \E t2 \in Time : 
                           (state_time' = t2                        
                        /\ Send([type |-> "1a", cord |-> c , 
                                 val |-> cordVal[c]], t2))

(***************************************************************************)
(* Phase 1b: If a replica receives a "1a" message, it replies with a "1b"  *)
(* message and learns the value                                            *)
(***************************************************************************)
Phase1b_learn(r,t) ==   
          \E t2 \in Time :  
                           (state_time' = t2
                        /\ knowVal' = [knowVal EXCEPT ![r] = TRUE])    
        
Phase1b(r,m,t) ==
          \E t2 \in Time :  
                           (state_time' = t2 
                        /\ Send([type |-> "1b", cord |-> m.cord, rep |-> r], t2))                                                    

(***************************************************************************)
(* Phase 2a: If the coordinator receives "1b" messages from all replicas   *)
(* it sends a "2a" message to all replicas                                 *)
(***************************************************************************)
Phase2a(c,t) == 
          \E t2 \in Time :  
                           (state_time' = t2 
                        /\ Send([type |-> "2a", cord |-> c], t2))


(***************************************************************************)
(* Phase 2b: If areplica receives a "2a" message from a coordinator        *)
(* it knows that all other replicas have also committed thesame value      *)
(***************************************************************************)
Phase2b_learn(r,t) == 
          \E t2 \in Time : 
                           (state_time' = t2 
                        /\ allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE])

                 
Phase2b(r,m,t) == 
          \E t2 \in Time : 
                           (state_time' = t2 
                        /\ Send([type |-> "2b", cord |-> m.cord, rep |-> r], t2))
                              
(***************************************************************************)
(* Learning: If 2b messages for all replica are delivered to a coordinator *)
(* then the coodinator knows that the `^$E^2_{G}\phi$ ^' has been attained *)
(***************************************************************************)
Phase2c_learn(c,t) ==   
          \E t2 \in Time : 
                           (state_time' = t2 
                        /\ safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE])
                            
(***************************************************************************)
(*  The type of possible messages                                          *)
(***************************************************************************)
Messages ==    [type : {"1a"}, cord : Coordinators, val : Values]
          \cup [type : {"1b"}, cord : Coordinators, rep : Replicas]
          \cup [type : {"2a"}, cord : Coordinators]
          \cup [type : {"2b"}, cord : Coordinators, rep : Replicas]       


(***************************************************************************)
(*  The following section specifies rules and predicates that define       *)
(*  availability and the behaviour of available agents                     *)
(***************************************************************************)
\*Defining Availability as an abstract prediate that can either be true or false
CONSTANT Available(_, _)
ASSUME \A x, t : Available(x,t) \in BOOLEAN

\*Always Available
Always_available(x) == \A t \in Time : Available(x,t)

(***************************************************************************)
(*Rules for Coordinators                                                   *)
(***************************************************************************)

Rule_1a_msg(c,t) == 
  (~(\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord = c))
    <=> Phase1a(c,t)


Rule_2a_msg(c,t) ==
     (\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord = c)
     <=> Phase2a(c,t)

Rule_2c_learn(c,t) ==
  (\A r \in Replicas : (\E m \in msgs : m.type = "2b" /\ m.rep = r /\ m.cord = c))
   <=> (Phase2c_learn(c,t))
   

(***************************************************************************)
(*Rules for Replicas                                                       *)
(***************************************************************************)
Rule_1b_msg(r,t) == 
 \A c \in Coordinators :
  (
    (\E m \in msgs : \E v \in Values: m.type = "1a" 
                                   /\ m.cord = c
                                   /\ m.val = v)
      =>   (\E m \in msgs : \E v \in Values: m.type = "1a" 
                                          /\ m.cord = c
                                          /\ m.val = v   
                                          /\ Phase1b(r,m,t))
  )


Rule_1b_learn(r,t) ==
   (Phase1b_learn(r,t) <=>   (\E m \in msgs : Send([type |-> "1b", cord |-> m.cord, rep |-> r], t)))
/\ (Phase1b_learn(r,t) <=>   (\E c \in Coordinators: \E m \in msgs : m.type = "1a" /\ m.cord = c))                          
                       
      
 
Rule_2b_msg(r,t) == 
 \A c \in Coordinators :
  (
    (\E m \in msgs : m.type = "2a" /\ m.cord = c)
       
           =>  (\E m \in msgs : m.type = "2a" /\ m.cord = c   
                                              /\ Phase2b(r,m,t) )
  )                                        


Rule_2b_learn(r,t) ==
   (Phase2b_learn(r,t) <=>   (\E m \in msgs : Send([type |-> "2b", cord |-> m.cord, rep |-> r], t)))
/\ (Phase2b_learn(r,t) <=>   (\E c \in Coordinators: \E m \in msgs : m.type = "2a" /\ m.cord = c))                          
                       

      
(***************************************************************************)
(*Non-Byzantine behavior of agents                                         *)
(***************************************************************************) 
\*A coordinator's state-dependent expected behavior
\*Each state has an associated time and depending on context (state or state'),  
\*it can either be state_time or state_time'                                        
Coordinator_behavior == 
(\A c \in Coordinators : 
      \A t \in Time : ( ( (\/ state_time = t \/ state_time' = t) 
                             /\ Available(c,t)) =>       
                                             /\ Rule_1a_msg(c,t)                                                                                                          
                                             /\ Rule_2a_msg(c,t)
                                             /\ Rule_2c_learn(c,t) ) )

\*A replica's state-dependent expected behavior 
\*Each state has an associated time and depending on context(state or state'), 
\*it can either be state_time or state_time' 
Replica_behavior == 
(\A r \in Replicas : 
      \A t \in Time : ( ( (\/ state_time = t \/ state_time' = t)
                             /\ Available(r,t)) =>   
                                         /\ Rule_1b_msg(r,t)  
                                         /\ Rule_1b_learn(r,t)
                                         /\ Rule_2b_msg(r,t)
                                         /\ Rule_2b_learn(r,t) ) ) 

(***************************************************************************)
(*The following section specifies assumptions for proving progress         *)
(***************************************************************************)
\*All replicas are always available
allReplicasAlwaysAvailable ==  \A r \in Replicas : Always_available(r)

\* A coordinator is always available
existsCoordinatorAlwaysAvailable == \E c \in Coordinators : Always_available(c)


aAvailability ==    allReplicasAlwaysAvailable
                 /\ existsCoordinatorAlwaysAvailable

aBehavior ==  Coordinator_behavior
           /\ Replica_behavior

\* The set of replicas is non-empty
aNonEmptyReplicas == \E r \in Replicas : Always_available(r)

\* Guaranteed Message Delivery: all messages that are sent will be eventually delivered 
aDelivery == 
    \* 1a msg
 /\  \A c \in Coordinators : \A v \in Values : \A t \in Time : 
        Send([type |-> "1a", cord |-> c, val |-> v], t) => 
           \E t2 \in Time : (t2 > t) /\ Deliver([type |-> "1a", cord |-> c, 
                                                 val |-> v],t2)
                                                      
     \* 1b msg  Deliver([type |-> "1b", cord |-> m.cord, val |-> m.val, rep |-> r]                                              
 /\  \A r \in Replicas : \A m \in msgs : \A t \in Time :                                             
        Send([type |-> "1b", cord |-> m.cord, rep |-> r],t) =>
           \E t2 \in Time : (t2 > t) /\ Deliver ([type |-> "1b", 
                                                  cord |-> m.cord, 
                                                  rep |-> r],t2)
                                                  
 /\   \* 2a msg  Deliver([type |-> "2a", cord |-> c], t2)
       \A c \in Coordinators : \A t \in Time :
              Send([type |-> "2a", cord |-> c], t)
               <=>  \E t2 \in Time : (t2 > t) /\ Deliver([type |-> "2a", cord |-> c], t2)                                                   

      
 /\     \* 2b message Send([type |-> "2b", cord |-> m.cord, rep |-> r]         
        \A r \in Replicas : \A m \in msgs : \A t \in Time :                                             
        Send([type |-> "2b", cord |-> m.cord, rep |-> r],t) =>
           \E t2 \in Time : (t2 > t) /\ Deliver ([type |-> "2b", 
                                                  cord |-> m.cord,  
                                                  rep |-> r],t2)                                                  

\* Messages Cannot Be Corrupted: if a message exists in the system state, 
\* then it must have been sent 
aNoCorruption ==
    (    
        \A r \in Replicas: \A m \in msgs :
        ( 
           (m.type = "2b" /\ m.rep = r)
        => (\E t \in Time : state_time' = t /\ Available(r,t) /\ Send([type |-> "2b", cord |-> m.cord, rep |-> r],t)) 
        )
    )            
/\  (
        \A c \in Coordinators : \A m \in msgs : 
                ( 
                   (m.type = "2a" /\ m.cord = c)
                => (\E t2 \in Time : state_time' = t2 /\ Available(c,t2) /\ Send([type |-> "2a", cord |-> c],t2)) 
                )
    )        
/\  (    
        \A r \in Replicas : \A m \in msgs : 
        ( 
           ((m.type = "1b" /\ m.rep = r))
        => (\E t \in Time : state_time' = t /\ Available(r,t) /\ Send([type |-> "1b", cord |-> m.cord, rep |-> r],t)) 
        )
    ) 
 
        
                      
\* Additional system properties
aSysProps ==     msgs \in SUBSET Messages
            /\ cordVal \in  [Coordinators -> Values]
            /\ temporalProperties

\* progress assertions
pAssertions ==    aAvailability
               /\ aDelivery
               /\ aNonEmptyReplicas
               /\ aBehavior
               /\ aSysProps

\* safety assertions
sAssertions ==   allReplicasAlwaysAvailable
               /\ aNoCorruption
               /\ aBehavior
               /\ aSysProps
-----------------------------------------------------------------------------               
(***************************************************************************)
(*The proof                                                                *)
(***************************************************************************)   

\* Lemma - if a coordinator is available, 1a messages from it will be eventually 
\* delivered if it has not received 1b messsages from all replicas
LEMMA Lemma1 ==
 \A c \in Coordinators :
 (
   (\E t \in Time : Available(c,t)
                 /\ state_time = t
                 /\ (~(\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord = c)))
   /\ pAssertions              
   =>              
   (\E t \in Time : 
                 /\ state_time' = t
                 /\ (\E m \in msgs' : \E v \in Values  : m.cord = c /\  m.type = "1a" /\ m.val = v)) 
 
 )
<1> SUFFICES ASSUME NEW c \in Coordinators, pAssertions, 
                        (\E t \in Time : Available(c,t)
                                     /\ state_time = t
                                     /\  (~(\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord = c)))
                                     
    PROVE
           (\E t \in Time :
                         /\ state_time' = t
                         /\ (\E m \in msgs' : \E v \in Values  : m.cord = c /\  m.type = "1a" /\ m.val = v)) 

    OBVIOUS
<1>1. (\E t \in Time : Available(c,t)
                    /\ state_time = t
                    /\  (~(\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord = c)))
    OBVIOUS
<1>2. aBehavior /\ aDelivery /\ aSysProps
    BY DEF pAssertions
<1>3. Coordinator_behavior
    BY <1>2 DEF aBehavior  
<1>4. (\E t \in Time : Available(c,t)
                    /\ state_time = t
                    /\  (~(\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord = c))
                    /\ Rule_1a_msg(c,t) )
    BY <1>1, <1>3 DEF Coordinator_behavior     
<1>5. (\E t \in Time : Available(c,t)
                    /\ state_time = t
                    /\ (~(\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord = c))
                    /\ Rule_1a_msg(c,t) 
                    /\ ( \E t2 \in Time : Phase1a(c,t2)))
    BY <1>4 DEF Rule_1a_msg                                          
<1>6. (\E t \in Time : Available(c,t)
                    /\ state_time = t
                    /\ (~(\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord = c))
                    /\ Rule_1a_msg(c,t) 
                    /\ ( \E t2 \in Time : Send([type |-> "1a", cord |-> c , 
                                                val |-> cordVal[c]], t2)))
    BY <1>5 DEF Phase1a
<1>6a. cordVal[c] \in Values
    BY <1>2 DEF aSysProps    
<1>7. ( \E t2 \in Time : Deliver([type |-> "1a", cord |-> c , val |-> cordVal[c]], t2))
    BY <1>6, <1>6a, <1>2 DEF aDelivery  
<1>8. ( \E t2 \in Time : (state_time' = t2) 
                      /\ (msgs' = msgs \cup {[type |-> "1a", cord |-> c , val |-> cordVal[c]]}) ) 
    BY <1>7 DEF Deliver                                
<1>9. ( \E t2 \in Time : (state_time' = t2) 
                      /\ \E v \in Values : ([type |-> "1a", cord |-> c , val |-> v] \in msgs') ) 
    BY <1>8, <1>6a
<1>10. ( \E t2 \in Time : (state_time' = t2) 
                      /\ \E v \in Values : \E m \in msgs' : m.type = "1a" /\  m.cord = c /\ m.val = v )  
    BY <1>9   
<1>200. QED
   BY <1>10




\* Lemma - If 1a messages from a coordinator have been delivered, eventually
\* 1b messages for P from all replicas will be delivered
LEMMA Lemma2 == 
  \A c \in Coordinators :
  (
   ( \E t2 \in Time :    state_time = t2 
                      /\ \E v \in Values : \E m \in msgs : m.type = "1a" /\  m.cord = c /\ m.val = v)
   /\ pAssertions
   => 
   ( \E t2 \in Time :    state_time' = t2 
                      /\ \A r \in Replicas : \E m \in msgs' : m.type = "1b" /\  m.cord = c /\ m.rep = r)                        
  )
<1> SUFFICES ASSUME NEW c \in Coordinators, pAssertions,
        (\E t2 \in Time : state_time = t2 
                       /\ \E v \in Values : \E m \in msgs : m.type = "1a" /\  m.cord = c /\ m.val = v)
             PROVE (\E t2 \in Time : state_time' = t2 
                       /\ \A r \in Replicas : \E m \in msgs' : m.type = "1b" /\  m.cord = c /\ m.rep = r)
    OBVIOUS
<1>1. (\E t2 \in Time : state_time = t2 
                     /\ \E v \in Values : \E m \in msgs : m.type = "1a" /\  m.cord = c /\ m.val = v)
    OBVIOUS
<1>2. aBehavior /\ aDelivery /\ aSysProps /\ aAvailability
    BY DEF pAssertions
<1>3. Coordinator_behavior
    BY <1>2 DEF aBehavior 
<1>4. \A r \in Replicas : Always_available(r)
    BY <1>2 DEF aAvailability, allReplicasAlwaysAvailable    
<1>5.  (\E t2 \in Time : state_time = t2 
                     /\ (\E v \in Values : \E m \in msgs : m.type = "1a" /\  m.cord = c /\ m.val = v)
                     /\ (\A r \in Replicas : Available(r,t2)))
    BY <1>4, <1>1 DEF Always_available        
<1>5a. (\A r \in Replicas : 
         \A t \in Time : (state_time = t /\ Available(r,t)) =>
                                             /\ Rule_1b_msg(r,t)  
                                             /\ Rule_2b_msg(r,t) )  
    BY <1>2 DEF aBehavior, Replica_behavior                                            
<1>6. (\E t2 \in Time : state_time = t2 
                     /\ (\E v \in Values : \E m \in msgs : m.type = "1a" /\  m.cord = c /\ m.val = v)
                     /\ \A r \in Replicas : Available(r,t2))
    BY <1>5       
<1>7.\A r \in Replicas : \E t2 \in Time :
                        state_time = t2 
                     /\ Available(r,t2)
                     /\ (\E v \in Values : \E m \in msgs : m.type = "1a" /\  m.cord = c /\ m.val = v)                    
    BY <1>6      
<1>8.\A r \in Replicas : \E t2 \in Time :
                        state_time = t2 
                     /\ Rule_1b_msg(r,t2) 
                     /\ (\E v \in Values : \E m \in msgs : m.type = "1a" /\  m.cord = c /\ m.val = v)                    
    BY <1>7, <1>5a
<1>9.\A r \in Replicas : \E t2 \in Time :
                        state_time = t2 
                     /\  \E m \in msgs : (\E v \in Values : m.type = "1a" /\  m.cord = c  /\ m.val = v)                     
                     /\  Rule_1b_msg(r,t2)                     
    BY <1>8   
<1>10.\A r \in Replicas : 
                     /\  \E m \in msgs : (\E v \in Values : m.type = "1a" /\  m.cord = c  /\ m.val = v)                  
                                      /\ \E t \in Time : Phase1b(r,m,t)                 
    BY <1>9 DEF Rule_1b_msg     
<1>11.\A r \in Replicas : 
                     /\  \E m \in msgs : (m.type = "1a" /\  m.cord = c)                    
                                     /\ \E t \in Time : Send([type |-> "1b", cord |-> m.cord, rep |-> r], t)                                                        
    BY <1>10 DEF Phase1b                                                  
<1>12.\A r \in Replicas : 
                     /\  \E m \in msgs : m.type = "1a" /\  m.cord = c                    
                                     /\ \E t \in Time : Deliver([type |-> "1b", cord |-> m.cord, rep |-> r], t)                                                        
    BY <1>11, <1>2 DEF aDelivery 
<1>13.\A r \in Replicas : 
                     /\  \E m \in msgs : m.type = "1a" /\  m.cord = c                    
                                     /\ \E t \in Time : state_time' = t
                                                     /\ msgs' = msgs \cup {[type |-> "1b", cord |-> m.cord, rep |-> r]}                                                        
    BY <1>12 DEF Deliver
<1>13a.\A r \in Replicas : 
                     /\  \E m \in msgs : m.type = "1a" /\  m.cord = c                    
                                     /\ \E t \in Time : state_time' = t
                                                     /\ msgs' = msgs \cup {[type |-> "1b", cord |-> c,  rep |-> r]}                                                        
    BY <1>13 
<1>14.\A r \in Replicas : 
                     /\  \E m \in msgs : m.type = "1a" /\  m.cord = c     
                                     /\ \E t \in Time : state_time' = t
                                                     /\ [type |-> "1b", cord |-> c,  rep |-> r] \in msgs'                                                        
    BY <1>13                                                                                                                
<1>15.\A r \in Replicas : 
                     /\ \E t \in Time : state_time' = t
                                     /\ \E m \in msgs' : m.type = "1b" /\  m.cord = c /\ m.rep = r                                                       
    BY <1>14 
<1>16.  \E t \in Time : state_time' = t
                     /\ \A r \in Replicas : \E m \in msgs' : m.type = "1b" /\  m.cord = c /\ m.rep = r
    BY <1>2, <1>15 DEF aSysProps, temporalProperties, temporalProperty1                                                                                                                                           
<1>200. QED
   BY <1>16
   
   
   
   
\* Lemma - If 1b messages from all replicas have been delivered for a coordinator
\* which is available, eventually 2a messages from it will be delivered
LEMMA Lemma3 ==
 \A c \in Coordinators :
 (
   (\E t \in Time : Available(c,t)
                 /\ state_time = t
                 /\ ((\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord=c)))
   /\ pAssertions              
   =>              
   (\E t \in Time : 
                    state_time' = t
                 /\ (\E m \in msgs' : m.cord = c /\  m.type = "2a")) 
 
 )
 
 <1> SUFFICES ASSUME NEW c \in Coordinators, pAssertions, 
    (\E t \in Time : Available(c,t)
                 /\ state_time = t
                 /\ ((\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord=c)))
              PROVE     (\E t \in Time : 
                                        state_time' = t
                                     /\ (\E m \in msgs' : m.cord = c /\  m.type = "2a"))
     OBVIOUS                                 
<1>1. (\E t \in Time : Available(c,t)
                    /\ state_time = t
                    /\ ((\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord=c)))
     OBVIOUS
<1>2. aBehavior /\ aDelivery /\ aSysProps /\ aAvailability
    BY DEF pAssertions
<1>3. Coordinator_behavior
    BY <1>2 DEF aBehavior
<1>4. (\E t \in Time : Available(c,t)
                    /\ state_time = t
                    /\ Rule_2a_msg(c,t)
                    /\ ((\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord=c)))
    BY <1>1, <1>2 DEF aBehavior, Coordinator_behavior     
<1>5. \E t \in Time :
                       state_time = t
                    /\ Rule_2a_msg(c,t)
                    /\ (\E t2 \in Time : Phase2a(c,t2))             
    BY <1>4 DEF Rule_2a_msg
<1>6. (\E t2 \in Time : Send([type |-> "2a", cord |-> c], t2))             
    BY <1>5 DEF Phase2a
<1>7. (\E t2 \in Time : Deliver([type |-> "2a", cord |-> c], t2))             
    BY <1>6, <1>2 DEF aDelivery
<1>8. (\E t2 \in Time : state_time' = t2 /\ msgs' = msgs \cup{[type |-> "2a", cord |-> c]})             
    BY <1>7 DEF Deliver  
<1>9. (\E t2 \in Time : state_time' = t2 /\ [type |-> "2a", cord |-> c] \in msgs')             
    BY <1>8  
<1>10.  (\E t \in Time : 
                        state_time' = t
                     /\ (\E m \in msgs' : m.cord = c /\  m.type = "2a"))     
    BY <1>9                                  
 <1>200. QED
    BY <1>10



\* Lemma - If 2a messages from a coordinator have been delivered, eventually
\* 2b messages for P from all replicas will be delivered
LEMMA Lemma4 == 
  \A c \in Coordinators :
  (
   ( \E t2 \in Time :    state_time = t2 
                      /\ \E m \in msgs : m.type = "2a" /\  m.cord = c)
   /\ pAssertions
   => 
   ( \E t2 \in Time :    state_time' = t2 
                      /\ \A r \in Replicas : \E m \in msgs' : m.type = "2b" /\  m.cord = c /\ m.rep = r)                        
  )
<1> SUFFICES ASSUME NEW c \in Coordinators, pAssertions,
                       ( \E t2 \in Time :    state_time = t2 
                                          /\ \E m \in msgs : m.type = "2a" /\  m.cord = c)              
             PROVE                              
   ( \E t2 \in Time :    state_time' = t2 
                      /\ \A r \in Replicas : \E m \in msgs' : m.type = "2b" /\  m.cord = c /\ m.rep = r)                        
    OBVIOUS                  
<1>1. (\E t2 \in Time : state_time = t2 
                     /\ \E m \in msgs : m.type = "2a" /\  m.cord = c)
    OBVIOUS
<1>2. aBehavior /\ aDelivery /\ aSysProps /\ aAvailability
    BY DEF pAssertions
<1>3. Coordinator_behavior
    BY <1>2 DEF aBehavior 
<1>4. \A r \in Replicas : Always_available(r)
    BY <1>2 DEF aAvailability, allReplicasAlwaysAvailable    
<1>5.  (\E t2 \in Time : state_time = t2 
                     /\ (\E m \in msgs : m.type = "2a" /\  m.cord = c)
                     /\ (\A r \in Replicas : Available(r,t2)))
    BY <1>4, <1>1 DEF Always_available        
<1>5a. (\A r \in Replicas : 
        \A t \in Time : (state_time = t /\ Available(r,t)) => 
                                            /\ Rule_1b_msg(r,t)  
                                            /\ Rule_2b_msg(r,t) )  
    BY <1>2 DEF aBehavior, Replica_behavior                                            
<1>6. (\E t2 \in Time : state_time = t2 
                     /\ (\E m \in msgs : m.type = "2a" /\  m.cord = c )
                     /\ \A r \in Replicas : Available(r,t2))
    BY <1>5       
<1>7.\A r \in Replicas : \E t2 \in Time :
                        state_time = t2 
                     /\ Available(r,t2)
                     /\ (\E m \in msgs : m.type = "2a" /\  m.cord = c )                    
    BY <1>6      
<1>8.\A r \in Replicas : \E t2 \in Time :
                        state_time = t2 
                     /\ Rule_2b_msg(r,t2) 
                     /\ (\E m \in msgs : m.type = "2a" /\  m.cord = c)                    
    BY <1>7, <1>5a
<1>9.\A r \in Replicas : \E t2 \in Time :
                        state_time = t2 
                     /\  \E m \in msgs : ( m.type = "2a" /\  m.cord = c  )                     
                     /\  Rule_2b_msg(r,t2)                      
    BY <1>8
<1>10.\A r \in Replicas : 
                     /\  \E m \in msgs : ( m.type = "2a" /\  m.cord = c  )                     
                                       /\  \E t \in Time : Phase2b(r,m,t)                      
    BY <1>9 DEF Rule_2b_msg    
<1>11.\A r \in Replicas : 
                     /\  \E m \in msgs : m.type = "2a" /\  m.cord = c                    
                                     /\ \E t \in Time : Send([type |-> "2b", cord |-> m.cord, rep |-> r], t)                                                        
    BY <1>10 DEF Phase2b                                                  
<1>12.\A r \in Replicas : 
                     /\  \E m \in msgs : m.type = "2a" /\  m.cord = c                    
                                     /\ \E t \in Time : Deliver([type |-> "2b", cord |-> m.cord, rep |-> r], t)                                                        
    BY <1>11, <1>2 DEF aDelivery 
<1>13.\A r \in Replicas : 
                     /\  \E m \in msgs : m.type = "2a" /\  m.cord = c                    
                                     /\ \E t \in Time : state_time' = t
                                                     /\ msgs' = msgs \cup {[type |-> "2b", cord |-> m.cord,  rep |-> r]}                                                        
    BY <1>12 DEF Deliver
<1>13a.\A r \in Replicas : 
                     /\  \E m \in msgs : m.type = "2a" /\  m.cord = c                    
                                     /\ \E t \in Time : state_time' = t
                                                     /\ msgs' = msgs \cup {[type |-> "2b", cord |-> c, rep |-> r]}                                                        
    BY <1>13 
<1>14.\A r \in Replicas : 
                     /\  \E m \in msgs : m.type = "2a" /\  m.cord = c     
                                     /\ \E t \in Time : state_time' = t
                                                     /\ [type |-> "2b", cord |-> c, rep |-> r] \in msgs'                                                        
    BY <1>13                                                                                                                
<1>15.\A r \in Replicas : 
                     /\ \E t \in Time : state_time' = t
                                     /\ \E m \in msgs' : m.type = "2b" /\  m.cord = c /\ m.rep = r                                                       
    BY <1>14 
<1>16.  \E t \in Time : state_time' = t
                     /\ \A r \in Replicas : \E m \in msgs' : m.type = "2b" /\  m.cord = c /\ m.rep = r
    BY <1>2, <1>15 DEF aSysProps, temporalProperties, temporalProperty1                                                                                                                                           
<1>200. QED
       BY <1>16



(***************************************************************************)
(*The intermediate states                                                  *)
(***************************************************************************)
\* after a coordinator has sent 1a msgs 
msgsPost1a(c) ==
  Always_available(c)
/\ \E v \in Values : \E m \in msgs : m.type = "1a" /\  m.cord = c /\ m.val = v 

\* after a coordinator has received 1b messages from all replicas
msgsPost1b(c) ==
  Always_available(c)
/\ \A r \in Replicas : \E m \in msgs : m.type = "1b" /\  m.cord = c /\ m.rep = r

\* after a coordinator has sent 2a msgs
msgsPost2a(c) ==
  Always_available(c)
/\ \E m \in msgs : m.cord = c /\  m.type = "2a"

\* after a coordinator has received 2b messages from all replicas
msgsPost2b(c) ==
  Always_available(c)
/\ \A r \in Replicas : \E m \in msgs : m.type = "2b" /\  m.cord = c /\ m.rep = r
----------------------------------------------------------------------------

\* Eventually, there will be 1a messages from a coordinator
LEMMA Lemma5 ==
pAssertions =>
 \E c \in Coordinators:
  \E t \in Time: state_time = t
                 /\ msgsPost1a(c) 
<1> SUFFICES ASSUME pAssertions
             PROVE  \E c \in Coordinators:
                      \E t \in Time: state_time = t
                                     /\msgsPost1a(c)
    OBVIOUS
<1>1. aAvailability /\ aSysProps /\ aNonEmptyReplicas 
    BY DEF pAssertions 
<1>2. existsCoordinatorAlwaysAvailable
    BY <1>1 DEF aAvailability
<1>3. \E c \in Coordinators : Always_available(c)
    BY <1>2 DEF existsCoordinatorAlwaysAvailable
<1>4. \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time = t
                                            /\ (~(\E m \in msgs : m.cord = c)))
    BY <1>3, <1>1 DEF aSysProps, temporalProperties, temporalProperty2   
<1>5.  \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time = t
                                            /\ Available(c,t)
                                            /\ (~(\E m \in msgs : m.cord = c)))
    BY <1>4 DEF Always_available  
<1>5a.  \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time = t
                                            /\ Available(c,t)
                                            /\ \E r \in Replicas : Always_available(r)
                                            /\ (~(\E m \in msgs : m.cord = c)))
    BY <1>5, <1>1 DEF aNonEmptyReplicas      
<1>5b.  \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time = t
                                            /\ Available(c,t)
                                            /\ (\E r \in Replicas : Always_available(r))
                                            /\ (\E r \in Replicas : ~(\E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord = c)))
    BY <1>5a  
<1>5c.  \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time = t
                                            /\ Available(c,t)
                                            /\ (\E r \in Replicas : Always_available(r))
                                            /\ (~(\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord = c)))
    BY <1>5b  
<1>5d.  \E c \in Coordinators :  Always_available(c)
                          /\ (\E t \in Time : Available(c,t)
                                         /\ state_time = t
                                         /\ (~(\A r \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r /\ m.cord = c)))
    BY <1>5c     
<1>6.  \E t \in Time : \E c \in Coordinators :  Always_available(c)
                                            /\ state_time' = t                                          
                                            /\ \E v \in Values : \E m \in msgs' : m.type = "1a" /\  m.cord = c /\ m.val = v 
    BY <1>5d, Lemma1  
<1>7.  \E t \in Time : \E c \in Coordinators : 
                                  \E t2 \in Time: state_time = t2  
                                               /\  Always_available(c)                                        
                                               /\ \E v \in Values : \E m \in msgs : m.type = "1a" /\  m.cord = c /\ m.val = v 
    BY <1>6, <1>1 DEF  aSysProps, temporalProperties, temporalProperty3  
<1>8.  \E t \in Time : \E c \in Coordinators :  state_time = t                                          
                                             /\ msgsPost1a(c) 
    BY <1>7 DEF msgsPost1a                                                                         
<1>200. QED
        BY <1>8 




LEMMA Lemma6 ==
pAssertions =>
 \E c \in Coordinators:
  \E t \in Time: state_time = t
                 /\ msgsPost1b(c)
<1> SUFFICES ASSUME pAssertions
             PROVE  \E c \in Coordinators:
                      \E t \in Time: state_time = t
                                     /\msgsPost1b(c)
    OBVIOUS                 
<1>1. aAvailability /\ aSysProps /\ aNonEmptyReplicas 
    BY DEF pAssertions 
<1>4. \E c \in Coordinators:
                      \E t \in Time: state_time = t
                                     /\msgsPost1a(c) 
    BY Lemma5   
<1>5.  \E c \in Coordinators :
                           /\ \E t \in Time : state_time = t
                                            /\  Always_available(c)
                                            /\ \E v \in Values : \E m \in msgs : m.type = "1a" /\  m.cord = c /\ m.val = v 
    BY <1>4 DEF msgsPost1a 
<1>5a.  \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time' = t
                                            /\ \A r \in Replicas : \E m \in msgs' : m.type = "1b" /\  m.cord = c /\ m.rep = r)
    BY <1>5, Lemma2     
<1>6.  \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time = t
                                            /\ \A r \in Replicas : \E m \in msgs : m.type = "1b" /\  m.cord = c /\ m.rep = r)
    BY <1>5a, <1>1 DEF aSysProps, temporalProperties, temporalProperty3     
<1>8.  \E t \in Time : \E c \in Coordinators :  state_time = t                                          
                                             /\ msgsPost1b(c) 
    BY <1>6 DEF msgsPost1b                                                                         
<1>200. QED
        BY <1>8 




LEMMA Lemma7 ==
pAssertions =>
 \E c \in Coordinators:
  \E t \in Time: state_time = t
                 /\ msgsPost2a(c) 
<1> SUFFICES ASSUME pAssertions
             PROVE  \E c \in Coordinators:
                      \E t \in Time: state_time = t
                                     /\msgsPost2a(c)
    OBVIOUS
<1>1. aAvailability /\ aSysProps /\ aNonEmptyReplicas 
    BY DEF pAssertions 
<1>4. \E c \in Coordinators:
                      \E t \in Time: state_time = t
                                     /\msgsPost1b(c) 
    BY Lemma6  
<1>5.    \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time = t
                                            /\ \A r \in Replicas : \E m \in msgs : m.type = "1b" /\  m.cord = c /\ m.rep = r)
    BY <1>4 DEF msgsPost1b                                         

<1>6. \E c \in Coordinators :  Always_available(c)
                            /\ \E t \in Time :  state_time' = t                                          
                                             /\ \E m \in msgs' : m.cord = c /\  m.type = "2a"
    BY <1>5, Lemma3 DEF Always_available 
<1>7.   \E t \in Time :  \E c \in Coordinators : Always_available(c)
                                             /\  state_time = t                                          
                                             /\ \E m \in msgs : m.cord = c /\  m.type = "2a" 
    BY <1>6, <1>1 DEF  aSysProps, temporalProperties, temporalProperty3  
<1>8.  \E t \in Time : \E c \in Coordinators :  state_time = t                                          
                                             /\ msgsPost2a(c) 
    BY <1>7 DEF msgsPost2a                                                                         
<1>200. QED
        BY <1>8 




LEMMA Lemma8 ==
pAssertions =>
 \E c \in Coordinators:
  \E t \in Time: state_time = t
                 /\ msgsPost2b(c)
<1> SUFFICES ASSUME pAssertions
             PROVE  \E c \in Coordinators:
                      \E t \in Time: state_time = t
                                     /\msgsPost2b(c)
    OBVIOUS                 
<1>1. aAvailability /\ aSysProps /\ aNonEmptyReplicas 
    BY DEF pAssertions 
<1>4. \E c \in Coordinators:
                      \E t \in Time: state_time = t
                                     /\msgsPost2a(c) 
    BY Lemma7   
<1>5.  \E c \in Coordinators :
                           /\ \E t \in Time : state_time = t
                                            /\  Always_available(c)
                                            /\  \E m \in msgs : m.type = "2a" /\  m.cord = c  
    BY <1>4 DEF msgsPost2a 
<1>5a.  \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time' = t
                                            /\ \A r \in Replicas : \E m \in msgs' : m.type = "2b" /\  m.cord = c /\ m.rep = r)
    BY <1>5, Lemma4     
<1>6.  \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time = t
                                            /\ \A r \in Replicas : \E m \in msgs : m.type = "2b" /\  m.cord = c /\ m.rep = r)
    BY <1>5a, <1>1 DEF aSysProps, temporalProperties, temporalProperty3     
<1>8.  \E t \in Time : \E c \in Coordinators :  state_time = t                                          
                                             /\ msgsPost2b(c) 
    BY <1>6 DEF msgsPost2b                                                                         
<1>200. QED
        BY <1>8         
        
       

\* Safety Lemma1 - A Coordinator will not learn `^$E^2_{G}\phi$ ^' if there
\* is at least one replica which does not know `^$E_{G}\phi$ ^'

THEOREM Lemma9 ==
sAssertions =>
(
  \A t \in Time : \A c \in Coordinators :
                        ((  state_time' = t
                        /\ Available(c,t)    
                        /\ safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE]) 
 =>
 (\A r \in Replicas : allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]))
)
<1> SUFFICES ASSUME  sAssertions,   
                     NEW t \in Time, NEW c \in Coordinators,
                                          (  state_time' = t
                                          /\ Available(c,t)    
                                          /\ safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE]) 
             PROVE  (\A r \in Replicas : allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE])
    OBVIOUS
<1>1.( state_time' = t
                        /\ Available(c,t)    
                        /\ safeStateAttained'= [safeStateAttained EXCEPT ![c] = TRUE]) 
    OBVIOUS
<1>2. aBehavior /\  allReplicasAlwaysAvailable
    BY DEF sAssertions
<1>3.                      state_time' = t
                        /\ Available(c,t)    
                        /\ Phase2c_learn(c,t) 
    BY <1>1, <1>2 DEF aBehavior, Coordinator_behavior, Rule_2c_learn, Phase2c_learn   
<1>3a.  state_time = t /\ Available(c,t) => ((\A r \in Replicas : (\E m \in msgs : m.type = "2b" /\ m.rep = r /\ m.cord = c)) <=> Phase2c_learn(c,t))
    BY <1>2 DEF aBehavior, Coordinator_behavior, Rule_2c_learn      
<1>4. 
                           state_time' = t
                        /\ Available(c,t)    
                        /\ Phase2c_learn(c,t) 
                        /\ (\A r \in Replicas : (\E m \in msgs : m.type = "2b" /\ m.rep = r /\ m.cord = c))
    BY <1>1, <1>2 DEF aBehavior, Coordinator_behavior, Rule_2c_learn, Phase2c_learn         
<1>5.  (\A r \in Replicas : (\E m \in msgs : m.type = "2b" /\ m.rep = r /\ m.cord = c))
    BY <1>4
<1>5a1. \A r \in Replicas : (\E m \in msgs : m.type = "2b" /\ m.rep = r )
    BY <1>5    
<1>5a.
        \A r \in Replicas: 
        ( 
           (\E m \in msgs : (m.type = "2b" /\ m.rep = r))
        => (\E m \in msgs : \E t2 \in Time : state_time ' = t2 /\ Send([type |-> "2b", cord |-> m.cord, rep |-> r],t2)) 
        )
    BY DEF sAssertions, aNoCorruption
<1>5b.
                        \A r \in Replicas : (\E m \in msgs : (m.type = "2b" /\ m.rep = r ))
                                         /\  (\E m \in msgs : \E t2 \in Time : state_time ' = t2 /\ Send([type |-> "2b", cord |-> m.cord, rep |-> r],t2)) 
    BY <1>5, <1>5a  
<1>5c. 
         \A r \in Replicas : 
          (\E m \in msgs : \E t2 \in Time : state_time ' = t2 /\ Send([type |-> "2b", cord |-> m.cord, rep |-> r],t2)) 
    BY <1>5b                                                         
<1>5d. \A r \in Replicas :  
         \E t2 \in Time : state_time ' = t2
                       /\ \E m \in msgs : Send([type |-> "2b", cord |-> m.cord, rep |-> r],t2) 
    BY <1>5c 
<1>5e.  \A r \in Replicas :  
          \E t2 \in Time :
                   /\ state_time ' = t2  
                   /\ Available(r,t2)
                   /\ (\E m \in msgs : Send([type |-> "2b", cord |-> m.cord, rep |-> r],t2)) 
    BY <1>5d, <1>2 DEF allReplicasAlwaysAvailable, Always_available         
<1>5h. \A r \in Replicas :  
          \E t2 \in Time : 
                   /\ state_time ' = t2           
                   /\ Available(r,t2)
                   /\ (\E m \in msgs : Send([type |-> "2b", cord |-> m.cord, rep |-> r],t2)) 
                   /\ Phase2b_learn(r,t2)   
    BY <1>5e, <1>2 DEF aBehavior, Replica_behavior, Rule_2b_learn                            
<1>6. ASSUME (~ \A r \in Replicas : allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE])
      PROVE  FALSE               
    <2>1. (~ \A r \in Replicas : allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE])
      BY <1>6
    <2>2. ~(\A r \in Replicas : \E t2 \in Time: Phase2b_learn(r,t2))  
       BY <2>1 DEF Phase2b_learn       
    <2>9. FALSE       
       BY <1>5h, <2>2                                  
    <2>200. QED
       BY <2>9       
<1>200. QED
    BY <1>6                 
 
 
                         
                           
\* Safety Lemma2 - Forall replicas, `^$k_rE_{G}\phi$ ^' implies that
\* all replicas know `$\phi$'   
THEOREM Lemma10 ==
sAssertions =>
(    
    \A r \in Replicas : \A t2 \in Time :
       (
           (  state_time' = t2 
           /\ Available(r,t2)
           /\ (allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]))
           =>
            (\A r2 \in Replicas : knowVal' = [knowVal EXCEPT ![r2] = TRUE])                            
       ) 
)                        
<1> SUFFICES ASSUME sAssertions, NEW r \in Replicas, NEW t \in Time,
                     state_time' = t, Available(r,t),    
                     allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]       
             PROVE  (\A r2 \in Replicas : knowVal' = [knowVal EXCEPT ![r2] = TRUE])
    OBVIOUS
<1>1.  Available(r,t)
    /\ allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]
    OBVIOUS
<1>2. aSysProps /\ aBehavior
    BY DEF sAssertions 
<1>3.  Available(r,t)
    /\ allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]
    /\ (\E c \in Coordinators: \E m \in msgs : m.type = "2a" /\ m.cord = c)
    BY <1>1, <1>2 DEF aBehavior, Replica_behavior, Rule_2b_learn, Phase2b_learn
<1>4. aNoCorruption
    BY DEF sAssertions
<1>4a.        \A c \in Coordinators : \A m \in msgs : 
                ( 
                   (m.type = "2a" /\ m.cord = c)
                => (\E t2 \in Time : state_time' = t2 /\ Available(c,t2) /\ Send([type |-> "2a", cord |-> c],t2)) 
                )
    BY <1>4 DEF aNoCorruption       
<1>5.  Available(r,t)
    /\ allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]
    /\ (\E c \in Coordinators : (\E t2 \in Time : state_time' = t2 /\ Available(c,t2) /\ Send([type |-> "2a", cord |-> c],t2)) ) 
    BY <1>3, <1>4a 

<1>6.  Available(r,t)
    /\ allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]
    /\ (\E c \in Coordinators :  (\E t2 \in Time : state_time' = t2 /\ Available(c,t2) /\ Send([type |-> "2a", cord |-> c],t2)) 
                                               /\ Phase2a(c,t) )                           
    BY <1>5 DEF Phase2a
<1>6a. \A c \in Coordinators :
         \A t3 \in Time :
          (
           ( state_time' = t3 /\ Available(c,t3)) =>
           (
            (\A r2 \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r2 /\ m.cord = c)
            <=> Phase2a(c,t3)
           ) 
         )      
    BY <1>2 DEF aBehavior, Coordinator_behavior, Rule_2a_msg           
<1>7.  Available(r,t)
    /\ allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]
    /\ (\E c \in Coordinators :  (\E t2 \in Time : state_time' = t2 /\ Available(c,t2) /\ Send([type |-> "2a", cord |-> c],t2)) 
                              /\ (\A r2 \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r2 /\ m.cord = c))
    BY <1>6, <1>6a     
<1>8.  Available(r,t)
    /\ allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE] 
    /\ (\A r2 \in Replicas : \E m \in msgs : m.type = "1b" /\ m.rep = r2)
    BY <1>7 
<1>9.  Available(r,t)
    /\ allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE] 
    /\ (\A r2 \in Replicas : (\E m \in msgs : \E t2 \in Time : state_time' = t2 /\ Available(r2,t2) /\ Send([type |-> "1b", cord |-> m.cord, rep |-> r2],t2)) )
    BY <1>8, <1>4 DEF aNoCorruption   
<1>10. Available(r,t)
    /\ allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE] 
    /\ (\A r2 \in Replicas : (\E m \in msgs : \E t2 \in Time : state_time' = t2 /\ Available(r2,t2) /\ Send([type |-> "1b", cord |-> m.cord, rep |-> r2],t2)
                                                              /\ Phase1b_learn(r2,t) ) )
    BY <1>9, <1>2 DEF aBehavior, Replica_behavior, Rule_1b_learn              
<1>11. (\A r2 \in Replicas : Phase1b_learn(r2,t) 
                          /\ knowVal' = [knowVal EXCEPT ![r2] = TRUE])
    BY <1>10 DEF Phase1b_learn 
<1>200. QED
    BY <1>11                      


\*extra
THEOREM Lemma11 ==
sAssertions =>
(
 \A t \in Time :               
            (\E r \in Replicas : state_time' = t 
                             /\ Available(r,t)
                             /\ (allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]))
            =>   (\A r2 \in Replicas :  knowVal' = [knowVal EXCEPT ![r2] = TRUE])              
)
<1> SUFFICES ASSUME sAssertions, NEW t \in Time,
                   (\E r \in Replicas : state_time' = t 
                             /\ Available(r,t)
                             /\ (allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE])) 
             PROVE (\A r2 \in Replicas :  knowVal' = [knowVal EXCEPT ![r2] = TRUE])
    OBVIOUS
<1>1. (\E r \in Replicas : state_time' = t 
                             /\ Available(r,t)
                             /\ (allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]))
    OBVIOUS
<1>2. (\A r2 \in Replicas :  knowVal' = [knowVal EXCEPT ![r2] = TRUE])
    BY <1>1, Lemma10                           
<1>200. QED
    BY <1>2            


\*extra
THEOREM Lemma12 ==
sAssertions =>
(
 \A t \in Time :               
            (\E c \in Coordinators :
                               state_time' = t
                            /\ Available(c,t)    
                            /\ safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE]) 
            =>   (\A r \in Replicas : allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE])             
)
<1> SUFFICES ASSUME sAssertions, NEW t \in Time,
                    (\E c \in Coordinators :
                                       state_time' = t
                                    /\ Available(c,t)    
                                    /\ safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE]) 
             PROVE (\A r \in Replicas : allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE])     
    OBVIOUS
<1>1. (\E c \in Coordinators :
                       state_time' = t
                    /\ Available(c,t)    
                    /\ safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE]) 
    OBVIOUS
<1>2. (\A r \in Replicas : allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE])
    BY <1>1, Lemma9                           
<1>200. QED
    BY <1>2            
             

             
             
\* Safety
THEOREM Theorem1 ==
sAssertions =>
(
    (
     \A t \in Time :               
                (\E c \in Coordinators :
                                   state_time' = t
                                /\ Available(c,t)    
                                /\ safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE]) 
                =>   (\A r \in Replicas : knowVal' = [knowVal EXCEPT ![r] = TRUE]
                                       /\ allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE])             
    )
) 
<1> SUFFICES ASSUME sAssertions, NEW t \in Time,
              (\E c \in Coordinators :
                                   state_time' = t
                                /\ Available(c,t)    
                                /\ safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE])             
             PROVE (\A r \in Replicas : knowVal' = [knowVal EXCEPT ![r] = TRUE]
                                     /\ allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]) 
    OBVIOUS
<1>1. (\E c \in Coordinators :
                           state_time' = t
                        /\ Available(c,t)    
                        /\ safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE])
    OBVIOUS
<1>2. \A r \in Replicas : allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]
    BY <1>1, Lemma9
<1>3. allReplicasAlwaysAvailable  
    BY DEF sAssertions
<1>4. (\A r \in Replicas : allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]
                       /\ Available(r,t))
    BY <1>2, <1>3 DEF allReplicasAlwaysAvailable, Always_available  
<1>5. (\A r \in Replicas : allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]
                       /\ Available(r,t))
   /\ (\A r2 \in Replicas :  knowVal' = [knowVal EXCEPT ![r2] = TRUE])
    BY <1>4, Lemma10   
<1>6. (\A r \in Replicas : allKnowVal' = [allKnowVal EXCEPT ![r] = TRUE]
                       /\ Available(r,t)
                       /\ knowVal' = [knowVal EXCEPT ![r] = TRUE])
    BY <1>5                                                                 
<1>200 QED
    BY <1>6                 
 


\* Progress  
THEOREM Theorem2 ==
pAssertions =>
 (\E t \in Time : \E c \in Coordinators : state_time' = t /\ safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE])
<1> SUFFICES ASSUME pAssertions
             PROVE (\E t \in Time : \E c \in Coordinators : state_time' = t /\ safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE])
    OBVIOUS
<1>1.  \E t \in Time : \E c \in Coordinators :  state_time = t                                          
                                             /\ msgsPost2b(c)
    BY Lemma8
<1>2.   \E c \in Coordinators : 
                           /\ (\E t \in Time : state_time = t
                                            /\ Always_available(c)
                                            /\ \A r \in Replicas : \E m \in msgs : m.type = "2b" /\  m.cord = c /\ m.rep = r)
    BY <1>1 DEF msgsPost2b
<1>3. \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time = t
                                            /\ Available(c,t)
                                            /\ \A r \in Replicas : \E m \in msgs : m.type = "2b" /\  m.cord = c /\ m.rep = r) 
    BY <1>2 DEF Always_available
<1>4. aBehavior
    BY DEF pAssertions
<1>5. Coordinator_behavior
    BY <1>4 DEF aBehavior 
<1>6. \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time = t
                                            /\ Rule_2c_learn(c,t)
                                            /\ \A r \in Replicas : \E m \in msgs : m.type = "2b" /\  m.cord = c /\ m.rep = r) 
    BY <1>3, <1>5 DEF Coordinator_behavior    
<1>7. \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time = t
                                            /\ Rule_2c_learn(c,t)
                                            /\ Available(c,t)
                                            /\ (\A r \in Replicas : \E m \in msgs : m.type = "2b" /\  m.cord = c /\ m.rep = r)) 
    BY <1>6 DEF Always_available    
<1>8. \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time = t
                                            /\ Rule_2c_learn(c,t)
                                            /\ Available(c,t)
                                            /\ (Phase2c_learn(c,t))
                                            /\ (\A r \in Replicas : \E m \in msgs : m.type = "2b" /\  m.cord = c /\ m.rep = r)) 
    BY <1>7 DEF Rule_2c_learn  
<1>9. \E c \in Coordinators : Always_available(c)
                           /\ (\E t \in Time : state_time' = t
                                            /\ (safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE]) )
    BY <1>8 DEF Phase2c_learn  
<1>10. \E t2 \in Time : \E c \in Coordinators :
                           ((state_time' = t2 /\ safeStateAttained' = [safeStateAttained EXCEPT ![c] = TRUE]) )
    BY <1>9                                                                                                                                                
<1>200 QED
    BY <1>10    



                       
=============================================================================
\* Modification History
\* Last modified Sat Sep 12 15:22:52 EDT 2020 by pauls
\* Created Thu Nov 14 15:15:40 EST 2019 by pauls
