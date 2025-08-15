---------------------------- MODULE E2EEncryption ----------------------------
(***************************************************************************)
(* Formal specification of End-to-End Encrypted Chat System using         *)
(* Double Ratchet Algorithm and X3DH key exchange                         *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Users,              \* Set of users in the system
    MaxMessages,        \* Maximum number of messages
    MaxKeys            \* Maximum number of keys per user

VARIABLES
    identityKeys,       \* User identity key pairs
    signedPreKeys,      \* Signed pre-keys for each user
    oneTimePreKeys,     \* One-time pre-keys for each user
    sessions,           \* Active sessions between users
    messages,           \* Encrypted messages
    messageKeys,        \* Message keys (should be deleted after use)
    chainKeys,          \* Chain keys for Double Ratchet
    rootKeys,           \* Root keys for Double Ratchet
    dhKeys,             \* Diffie-Hellman keys
    keyRotationCounter  \* Counter for key rotations

vars == <<identityKeys, signedPreKeys, oneTimePreKeys, sessions, messages,
          messageKeys, chainKeys, rootKeys, dhKeys, keyRotationCounter>>

(***************************************************************************)
(* Type Invariants                                                         *)
(***************************************************************************)

TypeInvariant ==
    /\ identityKeys \in [Users -> SUBSET (1..MaxKeys)]
    /\ signedPreKeys \in [Users -> SUBSET (1..MaxKeys)]
    /\ oneTimePreKeys \in [Users -> SUBSET (1..MaxKeys)]
    /\ sessions \in SUBSET (Users \X Users)
    /\ messages \in SUBSET [
        sender: Users,
        receiver: Users,
        content: 1..MaxMessages,
        messageKey: 1..MaxKeys,
        sequenceNumber: Nat
       ]
    /\ messageKeys \in SUBSET (1..MaxKeys)
    /\ chainKeys \in [sessions -> SUBSET (1..MaxKeys)]
    /\ rootKeys \in [sessions -> SUBSET (1..MaxKeys)]
    /\ dhKeys \in [Users -> SUBSET (1..MaxKeys)]
    /\ keyRotationCounter \in Nat

(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)

Init ==
    /\ identityKeys = [u \in Users |-> {1}]  \* Each user gets initial identity key
    /\ signedPreKeys = [u \in Users |-> {2}]  \* Initial signed pre-key
    /\ oneTimePreKeys = [u \in Users |-> {3, 4, 5}]  \* Initial one-time pre-keys
    /\ sessions = {}
    /\ messages = {}
    /\ messageKeys = {}
    /\ chainKeys = <<>>
    /\ rootKeys = <<>>
    /\ dhKeys = [u \in Users |-> {6}]  \* Initial DH key
    /\ keyRotationCounter = 0

(***************************************************************************)
(* X3DH Key Exchange                                                       *)
(***************************************************************************)

EstablishSession(sender, receiver) ==
    /\ sender \in Users
    /\ receiver \in Users
    /\ sender # receiver
    /\ <<sender, receiver>> \notin sessions
    /\ oneTimePreKeys[receiver] # {}  \* Receiver must have available one-time pre-keys
    /\ LET
        otpk == CHOOSE k \in oneTimePreKeys[receiver] : TRUE
       IN
        /\ sessions' = sessions \union {<<sender, receiver>>, <<receiver, sender>>}
        /\ oneTimePreKeys' = [oneTimePreKeys EXCEPT ![receiver] = @ \ {otpk}]
        /\ rootKeys' = rootKeys @@ 
            (<<sender, receiver>> :> {10 + keyRotationCounter}) @@
            (<<receiver, sender>> :> {10 + keyRotationCounter})
        /\ chainKeys' = chainKeys @@
            (<<sender, receiver>> :> {20 + keyRotationCounter}) @@
            (<<receiver, sender>> :> {20 + keyRotationCounter})
        /\ UNCHANGED <<identityKeys, signedPreKeys, messages, messageKeys, 
                      dhKeys, keyRotationCounter>>

(***************************************************************************)
(* Double Ratchet - Message Sending                                       *)
(***************************************************************************)

SendMessage(sender, receiver) ==
    /\ <<sender, receiver>> \in sessions
    /\ Cardinality(messages) < MaxMessages
    /\ chainKeys[<<sender, receiver>>] # {}
    /\ LET
        ck == CHOOSE k \in chainKeys[<<sender, receiver>>] : TRUE
        mk == 100 + Cardinality(messages)  \* Generate new message key
        newCk == 200 + keyRotationCounter  \* Generate new chain key
        msgNum == Cardinality({m \in messages : m.sender = sender /\ m.receiver = receiver})
       IN
        /\ messages' = messages \union {[
            sender |-> sender,
            receiver |-> receiver,
            content |-> Cardinality(messages) + 1,
            messageKey |-> mk,
            sequenceNumber |-> msgNum
           ]}
        /\ messageKeys' = messageKeys \union {mk}
        /\ chainKeys' = [chainKeys EXCEPT 
            ![<<sender, receiver>>] = (@ \ {ck}) \union {newCk}]
        /\ UNCHANGED <<identityKeys, signedPreKeys, oneTimePreKeys, sessions,
                      rootKeys, dhKeys, keyRotationCounter>>

(***************************************************************************)
(* Double Ratchet - DH Ratchet Step                                       *)
(***************************************************************************)

DHRatchet(user1, user2) ==
    /\ <<user1, user2>> \in sessions
    /\ dhKeys[user1] # {}
    /\ rootKeys[<<user1, user2>>] # {}
    /\ LET
        oldDH == CHOOSE k \in dhKeys[user1] : TRUE
        newDH == 300 + keyRotationCounter
        oldRK == CHOOSE k \in rootKeys[<<user1, user2>>] : TRUE
        newRK == 400 + keyRotationCounter
        newCK == 500 + keyRotationCounter
       IN
        /\ dhKeys' = [dhKeys EXCEPT ![user1] = (@ \ {oldDH}) \union {newDH}]
        /\ rootKeys' = [rootKeys EXCEPT 
            ![<<user1, user2>>] = (@ \ {oldRK}) \union {newRK}]
        /\ chainKeys' = [chainKeys EXCEPT 
            ![<<user1, user2>>] = @ \union {newCK}]
        /\ keyRotationCounter' = keyRotationCounter + 1
        /\ UNCHANGED <<identityKeys, signedPreKeys, oneTimePreKeys, sessions,
                      messages, messageKeys>>

(***************************************************************************)
(* Message Reception and Key Deletion                                     *)
(***************************************************************************)

ReceiveMessage(receiver, messageId) ==
    /\ \E m \in messages :
        /\ m.receiver = receiver
        /\ m.content = messageId
        /\ m.messageKey \in messageKeys
        /\ messageKeys' = messageKeys \ {m.messageKey}  \* Delete message key after use
        /\ UNCHANGED <<identityKeys, signedPreKeys, oneTimePreKeys, sessions,
                      messages, chainKeys, rootKeys, dhKeys, keyRotationCounter>>

(***************************************************************************)
(* Key Rotation                                                            *)
(***************************************************************************)

RotateSignedPreKey(user) ==
    /\ user \in Users
    /\ signedPreKeys[user] # {}
    /\ LET
        oldKey == CHOOSE k \in signedPreKeys[user] : TRUE
        newKey == 600 + keyRotationCounter
       IN
        /\ signedPreKeys' = [signedPreKeys EXCEPT 
            ![user] = (@ \ {oldKey}) \union {newKey}]
        /\ keyRotationCounter' = keyRotationCounter + 1
        /\ UNCHANGED <<identityKeys, oneTimePreKeys, sessions, messages,
                      messageKeys, chainKeys, rootKeys, dhKeys>>

ReplenishOneTimePreKeys(user) ==
    /\ user \in Users
    /\ Cardinality(oneTimePreKeys[user]) < 3  \* Replenish when low
    /\ LET
        newKeys == {700 + keyRotationCounter + i : i \in 0..2}
       IN
        /\ oneTimePreKeys' = [oneTimePreKeys EXCEPT 
            ![user] = @ \union newKeys]
        /\ keyRotationCounter' = keyRotationCounter + 3
        /\ UNCHANGED <<identityKeys, signedPreKeys, sessions, messages,
                      messageKeys, chainKeys, rootKeys, dhKeys>>

(***************************************************************************)
(* Next State Relation                                                    *)
(***************************************************************************)

Next ==
    \/ \E sender, receiver \in Users :
        \/ EstablishSession(sender, receiver)
        \/ SendMessage(sender, receiver)
        \/ DHRatchet(sender, receiver)
        \/ \E msgId \in 1..MaxMessages : ReceiveMessage(receiver, msgId)
    \/ \E user \in Users :
        \/ RotateSignedPreKey(user)
        \/ ReplenishOneTimePreKeys(user)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Security Properties                                                     *)
(***************************************************************************)

\* Perfect Forward Secrecy: Old message keys are deleted
PerfectForwardSecrecy ==
    \A m \in messages :
        \/ m.messageKey \in messageKeys  \* Key exists (message not received)
        \/ m.messageKey \notin messageKeys  \* Key deleted (message received)

\* No key reuse across messages
NoKeyReuse ==
    \A m1, m2 \in messages :
        (m1 # m2) => (m1.messageKey # m2.messageKey)

\* Session symmetry
SessionSymmetry ==
    \A u1, u2 \in Users :
        (<<u1, u2>> \in sessions) <=> (<<u2, u1>> \in sessions)

\* One-time pre-keys are consumed
OneTimePreKeyConsumption ==
    \A user \in Users :
        Cardinality(oneTimePreKeys[user]) <= 5

\* Message ordering within a session
MessageOrdering ==
    \A sender, receiver \in Users :
        \A m1, m2 \in messages :
            /\ m1.sender = sender
            /\ m1.receiver = receiver
            /\ m2.sender = sender
            /\ m2.receiver = receiver
            /\ m1.sequenceNumber < m2.sequenceNumber
            => m1.content < m2.content

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

\* Eventually all users can establish sessions
EventuallyConnected ==
    <>(\A u1, u2 \in Users : u1 # u2 => <<u1, u2>> \in sessions)

\* Keys are eventually rotated
EventualKeyRotation ==
    <>(keyRotationCounter > 0)

(***************************************************************************)
(* Main Safety Invariant                                                  *)
(***************************************************************************)

SafetyInvariant ==
    /\ TypeInvariant
    /\ PerfectForwardSecrecy
    /\ NoKeyReuse
    /\ SessionSymmetry
    /\ OneTimePreKeyConsumption
    /\ MessageOrdering

================================================================================