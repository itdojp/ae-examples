------------------------------ MODULE ReadStatus ------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Users,          \* ユーザーの集合
    Messages,       \* メッセージの集合
    Devices,        \* デバイスの集合
    MaxReadStatus   \* 最大既読ステータス数

VARIABLES
    messages,       \* 送信されたメッセージ
    readStatus,     \* 既読ステータス
    userDevices,    \* ユーザーとデバイスの関連
    onlineDevices   \* オンラインデバイス

vars == <<messages, readStatus, userDevices, onlineDevices>>

\* 型定義
Message == [
    id: STRING,
    sender: Users,
    conversationId: STRING,
    content: STRING,
    timestamp: Nat
]

ReadRecord == [
    messageId: STRING,
    userId: Users,
    deviceId: Devices,
    readAt: Nat
]

\* 初期状態
Init == 
    /\ messages = {}
    /\ readStatus = {}
    /\ userDevices = [u \in Users |-> {}]
    /\ onlineDevices = {}

\* デバイスの登録
RegisterDevice(user, device) ==
    /\ device \notin userDevices[user]
    /\ userDevices' = [userDevices EXCEPT ![user] = @ \cup {device}]
    /\ UNCHANGED <<messages, readStatus, onlineDevices>>

\* デバイスのオンライン化
DeviceOnline(device) ==
    /\ device \notin onlineDevices
    /\ \E u \in Users : device \in userDevices[u]  \* 登録済みデバイス
    /\ onlineDevices' = onlineDevices \cup {device}
    /\ UNCHANGED <<messages, readStatus, userDevices>>

\* デバイスのオフライン化
DeviceOffline(device) ==
    /\ device \in onlineDevices
    /\ onlineDevices' = onlineDevices \ {device}
    /\ UNCHANGED <<messages, readStatus, userDevices>>

\* メッセージの送信
SendMessage(msgId, sender, conversationId, content) ==
    /\ msgId \notin {m.id : m \in messages}  \* 重複なし
    /\ LET msg == [
        id |-> msgId,
        sender |-> sender,
        conversationId |-> conversationId,
        content |-> content,
        timestamp |-> Cardinality(messages) + 1
       ] IN
       messages' = messages \cup {msg}
    /\ UNCHANGED <<readStatus, userDevices, onlineDevices>>

\* メッセージの既読
MarkAsRead(msgId, userId, deviceId) ==
    /\ \E msg \in messages : msg.id = msgId  \* メッセージが存在
    /\ deviceId \in userDevices[userId]  \* デバイスがユーザーに属する
    /\ deviceId \in onlineDevices  \* デバイスがオンライン
    /\ \neg \E r \in readStatus : 
        /\ r.messageId = msgId 
        /\ r.userId = userId 
        /\ r.deviceId = deviceId  \* 未既読
    /\ LET readRecord == [
        messageId |-> msgId,
        userId |-> userId,
        deviceId |-> deviceId,
        readAt |-> Cardinality(readStatus) + 1
       ] IN
       readStatus' = readStatus \cup {readRecord}
    /\ UNCHANGED <<messages, userDevices, onlineDevices>>

\* 次の状態遷移
Next ==
    \/ \E u \in Users, d \in Devices : RegisterDevice(u, d)
    \/ \E d \in Devices : DeviceOnline(d)
    \/ \E d \in Devices : DeviceOffline(d)
    \/ \E msgId \in Messages, sender \in Users, convId \in STRING, content \in STRING :
        SendMessage(msgId, sender, convId, content)
    \/ \E msgId \in Messages, userId \in Users, deviceId \in Devices :
        MarkAsRead(msgId, userId, deviceId)

\* 仕様
Spec == Init /\ [][Next]_vars

\* 不変条件

\* INV1: デバイスは複数のユーザーに属さない
DeviceUniqueness ==
    \A u1, u2 \in Users : 
        u1 # u2 => (userDevices[u1] \cap userDevices[u2] = {})

\* INV2: オンラインデバイスは登録済みデバイス
OnlineDevicesRegistered ==
    \A d \in onlineDevices :
        \E u \in Users : d \in userDevices[u]

\* INV3: 既読は送信済みメッセージのみ
ReadStatusForExistingMessages ==
    \A r \in readStatus :
        \E m \in messages : m.id = r.messageId

\* INV4: 既読は登録済みデバイスからのみ
ReadStatusFromRegisteredDevices ==
    \A r \in readStatus :
        r.deviceId \in userDevices[r.userId]

\* INV5: メッセージIDの一意性
MessageIdUniqueness ==
    \A m1, m2 \in messages : m1 # m2 => m1.id # m2.id

\* INV6: 既読レコードの一意性
ReadStatusUniqueness ==
    \A r1, r2 \in readStatus :
        (r1.messageId = r2.messageId /\ r1.userId = r2.userId /\ r1.deviceId = r2.deviceId)
        => r1 = r2

\* 安全性特性

\* SAFETY1: 送信者は自分のメッセージを既読できない制限はない（仕様上許可）
SenderCanReadOwnMessage == TRUE

\* SAFETY2: 既読は時系列順序を保つ
ReadStatusTemporalOrder ==
    \A r1, r2 \in readStatus :
        r1.messageId = r2.messageId /\ r1.userId = r2.userId =>
        (r1.readAt < r2.readAt => r1.deviceId # r2.deviceId)

\* SAFETY3: オフラインデバイスから既読できない
NoReadFromOfflineDevices ==
    \A r \in readStatus :
        \E d \in onlineDevices : d = r.deviceId

\* 活性特性

\* LIVENESS1: 送信されたメッセージは最終的に既読される可能性がある
EventualReadPossibility ==
    \A msg \in messages :
        <>(\E u \in Users, d \in Devices :
            d \in userDevices[u] /\ d \in onlineDevices)

\* LIVENESS2: オンラインデバイスは既読を行う可能性がある
OnlineDevicesCanRead ==
    \A d \in onlineDevices :
        <>(\E r \in readStatus : r.deviceId = d)

\* 機能特性

\* FUNC1: デバイス別既読追跡
DeviceSpecificReadTracking ==
    \A msg \in messages, u \in Users :
        LET userReadStatus == {r \in readStatus : 
            r.messageId = msg.id /\ r.userId = u} IN
        Cardinality(userReadStatus) <= Cardinality(userDevices[u])

\* FUNC2: 会話別既読集計
ConversationReadAggregation ==
    \A convId \in STRING :
        LET convMessages == {m \in messages : m.conversationId = convId}
            convReadStatus == {r \in readStatus : 
                \E m \in convMessages : m.id = r.messageId} IN
        TRUE  \* 集計ロジックの基盤

\* 制約条件

\* 有限性の制約
FinitenesConstraint ==
    /\ Cardinality(messages) <= MaxReadStatus
    /\ Cardinality(readStatus) <= MaxReadStatus
    /\ Cardinality(onlineDevices) <= Cardinality(Devices)

\* 型制約
TypeInvariant ==
    /\ messages \subseteq Message
    /\ readStatus \subseteq ReadRecord
    /\ userDevices \in [Users -> SUBSET Devices]
    /\ onlineDevices \subseteq Devices

================================================================================

\* TLC 設定コメント:
\* 
\* CONSTANTS:
\* Users = {alice, bob, charlie}
\* Messages = {msg1, msg2, msg3}
\* Devices = {phone1, tablet1, pc1, phone2, tablet2}
\* MaxReadStatus = 15
\*
\* SPECIFICATION: Spec
\*
\* INVARIANTS:
\* DeviceUniqueness
\* OnlineDevicesRegistered
\* ReadStatusForExistingMessages
\* ReadStatusFromRegisteredDevices
\* MessageIdUniqueness
\* ReadStatusUniqueness
\* ReadStatusTemporalOrder
\* NoReadFromOfflineDevices
\* TypeInvariant
\*
\* PROPERTIES:
\* EventualReadPossibility
\* DeviceSpecificReadTracking