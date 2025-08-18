---------------------------- MODULE E2EEncryptedChat ----------------------------
(* 
 * Phase 4: Formal Verification with TLA+
 * E2E暗号化チャットシステムの形式検証
 *)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Users,          \* ユーザーの集合
    Messages,       \* メッセージの集合
    Keys,           \* 暗号鍵の集合
    MaxMessages     \* 最大メッセージ数

VARIABLES
    userKeys,       \* 各ユーザーの現在の鍵ペア
    oldKeys,        \* 破棄された古い鍵
    messageQueue,   \* 送信待ちメッセージキュー
    sentMessages,   \* 送信済みメッセージ
    sessionState,   \* Double Ratchetセッション状態
    deviceKeys,     \* マルチデバイス用の鍵
    verifiedPairs   \* 検証済みユーザーペア

------------------------------------------------------------
\* 型定義
------------------------------------------------------------

MessageType == [
    sender: Users,
    recipient: Users,
    content: Messages,
    encrypted: BOOLEAN,
    key: Keys,
    timestamp: Nat
]

KeyPairType == [
    public: Keys,
    private: Keys,
    generated: Nat
]

SessionStateType == [
    user1: Users,
    user2: Users,
    rootKey: Keys,
    sendChainKey: Keys,
    recvChainKey: Keys,
    messageNumber: Nat
]

------------------------------------------------------------
\* 初期状態
------------------------------------------------------------

Init ==
    /\ userKeys = [u \in Users |-> 
        [public |-> CHOOSE k \in Keys : TRUE,
         private |-> CHOOSE k \in Keys : TRUE,
         generated |-> 0]]
    /\ oldKeys = {}
    /\ messageQueue = <<>>
    /\ sentMessages = {}
    /\ sessionState = {}
    /\ deviceKeys = [u \in Users |-> {}]
    /\ verifiedPairs = {}

------------------------------------------------------------
\* ヘルパー関数
------------------------------------------------------------

\* メッセージを暗号化できるか
CanEncrypt(sender, recipient) ==
    /\ sender \in Users
    /\ recipient \in Users
    /\ userKeys[recipient].public \in Keys

\* メッセージを復号できるか
CanDecrypt(user, message) ==
    /\ user = message.recipient
    /\ message.encrypted = TRUE
    /\ \/ userKeys[user].private = message.key
       \/ \E k \in deviceKeys[user]: k.private = message.key

\* Perfect Forward Secrecyが保たれているか
MaintainsPFS(message) ==
    /\ message.encrypted = TRUE
    /\ message.key \notin oldKeys
    /\ \A k \in oldKeys: 
        k # message.key

------------------------------------------------------------
\* アクション
------------------------------------------------------------

\* 新しい鍵ペアを生成
GenerateNewKeyPair(user) ==
    /\ user \in Users
    /\ userKeys' = [userKeys EXCEPT ![user] = 
        [public |-> CHOOSE k \in Keys \ {userKeys[user].public} : TRUE,
         private |-> CHOOSE k \in Keys \ {userKeys[user].private} : TRUE,
         generated |-> userKeys[user].generated + 1]]
    /\ oldKeys' = oldKeys \cup {userKeys[user].private}
    /\ UNCHANGED <<messageQueue, sentMessages, sessionState, deviceKeys, verifiedPairs>>

\* メッセージを送信
SendMessage(sender, recipient, content) ==
    /\ sender \in Users
    /\ recipient \in Users
    /\ sender # recipient
    /\ CanEncrypt(sender, recipient)
    /\ Len(sentMessages) < MaxMessages
    /\ LET newMessage == [
            sender |-> sender,
            recipient |-> recipient,
            content |-> content,
            encrypted |-> TRUE,
            key |-> userKeys[recipient].public,
            timestamp |-> Cardinality(sentMessages)
        ]
       IN
        /\ sentMessages' = sentMessages \cup {newMessage}
        /\ messageQueue' = Append(messageQueue, newMessage)
    /\ UNCHANGED <<userKeys, oldKeys, sessionState, deviceKeys, verifiedPairs>>

\* Double Ratchetによる鍵更新
RatchetForward(user1, user2) ==
    /\ {user1, user2} \subseteq Users
    /\ \E session \in sessionState:
        /\ session.user1 = user1
        /\ session.user2 = user2
        /\ sessionState' = (sessionState \ {session}) \cup 
            {[session EXCEPT 
                !.sendChainKey = CHOOSE k \in Keys \ {session.sendChainKey} : TRUE,
                !.messageNumber = session.messageNumber + 1]}
    /\ UNCHANGED <<userKeys, oldKeys, messageQueue, sentMessages, deviceKeys, verifiedPairs>>

\* デバイスを追加
AddDevice(user, deviceKey) ==
    /\ user \in Users
    /\ deviceKey \in Keys
    /\ deviceKeys' = [deviceKeys EXCEPT ![user] = deviceKeys[user] \cup {
        [public |-> deviceKey,
         private |-> CHOOSE k \in Keys : TRUE,
         generated |-> Cardinality(deviceKeys[user])]}]
    /\ UNCHANGED <<userKeys, oldKeys, messageQueue, sentMessages, sessionState, verifiedPairs>>

\* セキュリティ検証
VerifySecurityNumber(user1, user2) ==
    /\ {user1, user2} \subseteq Users
    /\ user1 # user2
    /\ verifiedPairs' = verifiedPairs \cup {{user1, user2}}
    /\ UNCHANGED <<userKeys, oldKeys, messageQueue, sentMessages, sessionState, deviceKeys>>

------------------------------------------------------------
\* Next状態
------------------------------------------------------------

Next ==
    \/ \E u \in Users: GenerateNewKeyPair(u)
    \/ \E s, r \in Users, m \in Messages: SendMessage(s, r, m)
    \/ \E u1, u2 \in Users: RatchetForward(u1, u2)
    \/ \E u \in Users, k \in Keys: AddDevice(u, k)
    \/ \E u1, u2 \in Users: VerifySecurityNumber(u1, u2)

------------------------------------------------------------
\* 不変条件
------------------------------------------------------------

\* 型不変条件
TypeInvariant ==
    /\ userKeys \in [Users -> KeyPairType]
    /\ oldKeys \subseteq Keys
    /\ messageQueue \in Seq(MessageType)
    /\ sentMessages \subseteq MessageType
    /\ sessionState \subseteq SessionStateType
    /\ verifiedPairs \subseteq SUBSET Users

\* セキュリティ不変条件

\* P1: すべてのメッセージは暗号化されている
AllMessagesEncrypted ==
    \A m \in sentMessages: m.encrypted = TRUE

\* P2: 送信者と受信者以外はメッセージを復号できない
MessageConfidentiality ==
    \A m \in sentMessages:
        \A u \in Users:
            (u # m.sender /\ u # m.recipient) => ~CanDecrypt(u, m)

\* P3: Perfect Forward Secrecyが維持される
PerfectForwardSecrecy ==
    \A m \in sentMessages: MaintainsPFS(m)

\* P4: 鍵の一意性
KeyUniqueness ==
    \A u1, u2 \in Users:
        u1 # u2 => userKeys[u1].private # userKeys[u2].private

\* P5: メッセージの順序保証
MessageOrdering ==
    \A m1, m2 \in sentMessages:
        (m1.sender = m2.sender /\ m1.recipient = m2.recipient /\ 
         m1.timestamp < m2.timestamp) =>
        \E i, j \in 1..Len(messageQueue):
            /\ i < j
            /\ messageQueue[i] = m1
            /\ messageQueue[j] = m2

------------------------------------------------------------
\* 時相論理プロパティ
------------------------------------------------------------

\* L1: 最終的にすべてのメッセージが配信される
EventualDelivery ==
    <>(\A m \in messageQueue: m \in sentMessages)

\* L2: 鍵は定期的に更新される
KeyRotation ==
    []<>(\E u \in Users: 
        \E k \in Keys: userKeys[u].public # k /\ userKeys'[u].public = k)

\* L3: 検証されたペアは永続する
VerificationPersistence ==
    \A pair \in verifiedPairs: [](pair \in verifiedPairs)

------------------------------------------------------------
\* 安全性プロパティ
------------------------------------------------------------

Safety ==
    /\ TypeInvariant
    /\ AllMessagesEncrypted
    /\ MessageConfidentiality
    /\ PerfectForwardSecrecy
    /\ KeyUniqueness
    /\ MessageOrdering

------------------------------------------------------------
\* 活性プロパティ
------------------------------------------------------------

Liveness ==
    /\ EventualDelivery
    /\ KeyRotation
    /\ VerificationPersistence

------------------------------------------------------------
\* 仕様
------------------------------------------------------------

Spec == 
    /\ Init 
    /\ [][Next]_<<userKeys, oldKeys, messageQueue, sentMessages, sessionState, deviceKeys, verifiedPairs>>
    /\ WF_<<userKeys, oldKeys, messageQueue, sentMessages, sessionState, deviceKeys, verifiedPairs>>(Next)

------------------------------------------------------------
\* テスト用の制約
------------------------------------------------------------

\* モデル検査のための状態空間制限
StateConstraint ==
    /\ Cardinality(sentMessages) <= MaxMessages
    /\ Cardinality(oldKeys) <= MaxMessages * 2
    /\ Len(messageQueue) <= MaxMessages

------------------------------------------------------------
\* 検証すべきプロパティ
------------------------------------------------------------

THEOREM Spec => [](Safety /\ Liveness)

==================================================================================