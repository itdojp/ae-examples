Feature: End-to-End Encrypted Messaging
  As a user
  I want to send and receive encrypted messages
  So that my communications remain private

  Background:
    Given the E2E chat system is initialized
    And users "Alice" and "Bob" are registered
    And both users have generated their key bundles

  Scenario: Establish encrypted session between two users
    Given "Alice" wants to chat with "Bob"
    And "Alice" has retrieved "Bob"'s public key bundle
    When "Alice" initiates a session with "Bob"
    Then X3DH key exchange should be performed
    And a shared secret should be established
    And Double Ratchet should be initialized
    And "Bob"'s one-time pre-key should be consumed

  Scenario: Send encrypted message
    Given "Alice" has an established session with "Bob"
    When "Alice" sends message "Hello Bob!" to "Bob"
    Then the message should be encrypted using AES-256-GCM
    And a new message key should be derived
    And the chain key should be updated
    And the message should include authentication tag
    And the encrypted message should be stored

  Scenario: Receive and decrypt message
    Given "Bob" has an established session with "Alice"
    And "Alice" has sent an encrypted message to "Bob"
    When "Bob" receives the message
    Then "Bob" should decrypt the message successfully
    And "Bob" should see "Hello Bob!"
    And the message key should be deleted after use
    And the chain key should be updated

  Scenario: Perfect Forward Secrecy through key rotation
    Given "Alice" and "Bob" have exchanged 10 messages
    When a DH ratchet step occurs
    Then new ephemeral keys should be generated
    And the root key should be updated
    And new chain keys should be derived
    And old message keys should be deleted
    And previous messages should not be decryptable with new keys

  Scenario: Handle out-of-order message delivery
    Given "Alice" has sent messages 1, 2, 3 to "Bob"
    When "Bob" receives messages in order 1, 3, 2
    Then "Bob" should decrypt message 1 successfully
    And "Bob" should store skipped key for message 2
    And "Bob" should decrypt message 3 successfully
    And "Bob" should decrypt message 2 using stored key
    And all messages should be displayed in correct order

  Scenario: Message delivery confirmation
    Given "Alice" has sent a message to "Bob"
    When "Bob" receives the message
    Then "Bob" should send a delivery receipt
    And "Alice" should see the message marked as "delivered"
    When "Bob" reads the message
    Then "Bob" should send a read receipt
    And "Alice" should see the message marked as "read"

  Scenario: Verify identity through safety numbers
    Given "Alice" and "Bob" have an established session
    When "Alice" views the safety number with "Bob"
    Then a unique safety number should be displayed
    And a QR code should be generated
    When "Alice" and "Bob" compare safety numbers out-of-band
    And the numbers match
    Then they can mark the conversation as verified

  Scenario: Detect potential MITM attack
    Given "Alice" and "Bob" have a verified conversation
    When "Bob"'s identity key changes unexpectedly
    Then "Alice" should receive a security warning
    And the safety number should change
    And "Alice" should be prompted to re-verify

  Scenario: Session recovery after device loss
    Given "Alice" has lost her device
    And "Alice" registers a new device
    When "Alice" restores from backup
    Then "Alice" should generate new device keys
    And existing sessions should be re-established
    But old message history should not be decryptable

  Scenario: Multi-device message synchronization
    Given "Alice" has two devices "Phone" and "Laptop"
    When "Alice" sends a message from "Phone"
    Then the message should be encrypted for "Bob"
    And the message should be encrypted for "Laptop"
    And "Laptop" should receive and decrypt the message
    And both devices should show consistent chat history