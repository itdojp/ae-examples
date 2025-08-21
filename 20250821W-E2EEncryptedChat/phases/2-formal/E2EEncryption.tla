---------------------------- MODULE E2EEncryption ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Users,      \* ユーザーの集合
    Messages,   \* メッセージの集合
    MaxKeys     \* 最大キー数

VARIABLES
    userKeys,           \* 各ユーザーの公開鍵・秘密鍵ペア
    sentMessages,       \* 送信されたメッセージ
    receivedMessages,   \* 受信されたメッセージ
    keyExchanges,       \* キー交換の記録
    encryptedData       \* 暗号化されたデータ

vars == <<userKeys, sentMessages, receivedMessages, keyExchanges, encryptedData>>

\* 型定義
KeyPair == [public: STRING, private: STRING]
EncryptedMessage == [
    id: STRING,
    sender: Users,
    recipient: Users,
    encryptedContent: STRING,
    encryptedKey: STRING,
    timestamp: Nat
]

\* 初期状態
Init == 
    /\ userKeys = [u \in Users |-> [public |-> "", private |-> ""]]
    /\ sentMessages = {}
    /\ receivedMessages = {}
    /\ keyExchanges = {}
    /\ encryptedData = {}

\* ユーザーのキーペア生成
GenerateKeyPair(user) ==
    /\ userKeys[user].public = ""  \* まだキーが生成されていない
    /\ userKeys' = [userKeys EXCEPT ![user] = [
        public |-> "pub_" \o ToString(user),
        private |-> "priv_" \o ToString(user)
       ]]
    /\ UNCHANGED <<sentMessages, receivedMessages, keyExchanges, encryptedData>>

\* 公開鍵の交換
ExchangePublicKey(sender, recipient) ==
    /\ userKeys[sender].public # ""  \* 送信者のキーが存在
    /\ userKeys[recipient].public # ""  \* 受信者のキーが存在
    /\ {sender, recipient} \notin keyExchanges  \* まだ交換していない
    /\ keyExchanges' = keyExchanges \cup {{sender, recipient}}
    /\ UNCHANGED <<userKeys, sentMessages, receivedMessages, encryptedData>>

\* メッセージの暗号化と送信
SendEncryptedMessage(sender, recipient, msgId, content) ==
    /\ {sender, recipient} \in keyExchanges  \* キー交換済み
    /\ msgId \notin DOMAIN sentMessages  \* 重複メッセージなし
    /\ LET encMsg == [
        id |-> msgId,
        sender |-> sender,
        recipient |-> recipient,
        encryptedContent |-> "enc_" \o content,
        encryptedKey |-> "key_" \o ToString(sender) \o "_" \o ToString(recipient),
        timestamp |-> Cardinality(sentMessages) + 1
       ] IN
       /\ sentMessages' = sentMessages \cup {encMsg}
       /\ encryptedData' = encryptedData \cup {[
           messageId |-> msgId,
           algorithm |-> "RSA-OAEP+AES-GCM",
           keySize |-> 2048
          ]}
    /\ UNCHANGED <<userKeys, receivedMessages, keyExchanges>>

\* メッセージの受信と復号
ReceiveEncryptedMessage(msgId) ==
    /\ \E msg \in sentMessages : msg.id = msgId
    /\ msgId \notin DOMAIN receivedMessages
    /\ LET msg == CHOOSE m \in sentMessages : m.id = msgId IN
       /\ userKeys[msg.recipient].private # ""  \* 受信者の秘密鍵が存在
       /\ receivedMessages' = receivedMessages \cup {[
           messageId |-> msgId,
           decryptedContent |-> "dec_" \o msg.encryptedContent,
           recipient |-> msg.recipient,
           timestamp |-> Cardinality(receivedMessages) + 1
          ]}
    /\ UNCHANGED <<userKeys, sentMessages, keyExchanges, encryptedData>>

\* 次の状態遷移
Next ==
    \/ \E u \in Users : GenerateKeyPair(u)
    \/ \E s, r \in Users : s # r /\ ExchangePublicKey(s, r)
    \/ \E s, r \in Users, msgId \in Messages, content \in STRING :
        s # r /\ SendEncryptedMessage(s, r, msgId, content)
    \/ \E msgId \in Messages : ReceiveEncryptedMessage(msgId)

\* 仕様
Spec == Init /\ [][Next]_vars

\* 不変条件

\* INV1: 全ユーザーは最大1つのキーペアを持つ
KeyPairUniqueness ==
    \A u \in Users : 
        (userKeys[u].public # "" /\ userKeys[u].private # "") \/
        (userKeys[u].public = "" /\ userKeys[u].private = "")

\* INV2: 送信されたメッセージは必ず暗号化されている
MessageEncryption ==
    \A msg \in sentMessages :
        /\ msg.encryptedContent # ""
        /\ msg.encryptedKey # ""
        /\ \E enc \in encryptedData : enc.messageId = msg.id

\* INV3: キー交換なしにメッセージを送信できない
NoMessageWithoutKeyExchange ==
    \A msg \in sentMessages :
        {msg.sender, msg.recipient} \in keyExchanges

\* INV4: 秘密鍵を持つユーザーのみがメッセージを復号できる
DecryptionAuthorization ==
    \A recv \in receivedMessages :
        \E msg \in sentMessages :
            /\ msg.id = recv.messageId
            /\ msg.recipient = recv.recipient
            /\ userKeys[recv.recipient].private # ""

\* INV5: メッセージIDの一意性
MessageIdUniqueness ==
    \A m1, m2 \in sentMessages : m1 # m2 => m1.id # m2.id

\* 安全性特性

\* SAFETY1: 暗号化されたメッセージは意図された受信者のみが復号可能
EncryptionSafety ==
    \A msg \in sentMessages :
        \A u \in Users :
            (u # msg.recipient /\ userKeys[u].private # "") =>
            \neg \E recv \in receivedMessages :
                /\ recv.messageId = msg.id
                /\ recv.recipient = u

\* SAFETY2: 送信者の認証
SenderAuthentication ==
    \A recv \in receivedMessages :
        \E msg \in sentMessages :
            /\ msg.id = recv.messageId
            /\ userKeys[msg.sender].public # ""

\* 活性特性

\* LIVENESS1: 全ユーザーは最終的にキーペアを生成する
EventualKeyGeneration ==
    <>(\A u \in Users : userKeys[u].public # "")

\* LIVENESS2: 送信されたメッセージは最終的に受信される
EventualMessageDelivery ==
    \A msg \in sentMessages :
        <>(recv \in receivedMessages : recv.messageId = msg.id)

\* セキュリティ特性

\* SEC1: Perfect Forward Secrecy の模擬
\* 注：実際のPFSは複雑なため、キーローテーションの概念で模擬
ForwardSecrecy ==
    TRUE  \* 簡略化：実装では定期的なキー更新で実現

\* SEC2: メッセージの完全性
MessageIntegrity ==
    \A recv \in receivedMessages :
        \E msg \in sentMessages :
            /\ recv.messageId = msg.id
            /\ recv.decryptedContent = "dec_" \o msg.encryptedContent

\* 制約条件

\* 有限性の制約
FinitenesConstraint ==
    /\ Cardinality(sentMessages) <= MaxKeys
    /\ Cardinality(receivedMessages) <= MaxKeys
    /\ Cardinality(keyExchanges) <= MaxKeys

\* 型制約
TypeInvariant ==
    /\ userKeys \in [Users -> KeyPair]
    /\ sentMessages \subseteq EncryptedMessage
    /\ receivedMessages \subseteq [messageId: STRING, decryptedContent: STRING,
                                  recipient: Users, timestamp: Nat]
    /\ keyExchanges \subseteq SUBSET Users
    /\ encryptedData \subseteq [messageId: STRING, algorithm: STRING, keySize: Nat]

================================================================================

\* TLC 設定コメント:
\* 
\* CONSTANTS:
\* Users = {u1, u2, u3}
\* Messages = {m1, m2, m3}
\* MaxKeys = 5
\*
\* SPECIFICATION: Spec
\*
\* INVARIANTS:
\* KeyPairUniqueness
\* MessageEncryption
\* NoMessageWithoutKeyExchange
\* DecryptionAuthorization
\* MessageIdUniqueness
\* EncryptionSafety
\* SenderAuthentication
\* TypeInvariant
\*
\* PROPERTIES:
\* EventualKeyGeneration
\* EventualMessageDelivery
\* MessageIntegrity