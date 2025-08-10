Feature: Cryptographic Key Management
  As a system administrator
  I want to ensure proper key lifecycle management
  So that the encryption remains secure over time

  Background:
    Given the E2E chat system is initialized
    And user "Alice" is registered with initial keys

  Scenario: Initial key generation
    When "Alice" registers for the first time
    Then the following keys should be generated:
      | Key Type           | Count | Algorithm  |
      | Identity Key       | 1     | Ed25519    |
      | Signed Pre-Key     | 1     | X25519     |
      | One-Time Pre-Keys  | 100   | X25519     |
    And all private keys should be stored securely
    And public keys should be uploaded to the server

  Scenario: Signed pre-key rotation
    Given "Alice"'s signed pre-key is 25 days old
    When the key rotation check runs
    Then a new signed pre-key should be generated
    And it should be signed with the identity key
    And the old key should be retained for 5 days
    And the new key should be uploaded to the server

  Scenario: One-time pre-key replenishment
    Given "Alice" has only 10 one-time pre-keys remaining
    When the key replenishment check runs
    Then 90 new one-time pre-keys should be generated
    And the keys should have sequential IDs
    And the new keys should be uploaded to the server

  Scenario: One-time pre-key consumption
    Given "Bob" wants to start a conversation with "Alice"
    When "Bob" fetches "Alice"'s key bundle
    Then the bundle should include:
      | Key Type          | Included |
      | Identity Key      | Yes      |
      | Signed Pre-Key    | Yes      |
      | One-Time Pre-Key  | Yes      |
    And the one-time pre-key should be marked as used
    And the used key should not be given out again

  Scenario: Key bundle without available one-time pre-keys
    Given "Alice" has no unused one-time pre-keys
    When "Charlie" fetches "Alice"'s key bundle
    Then the bundle should include:
      | Key Type          | Included |
      | Identity Key      | Yes      |
      | Signed Pre-Key    | Yes      |
      | One-Time Pre-Key  | No       |
    And X3DH should proceed without one-time pre-key

  Scenario: Verify signed pre-key signature
    Given "Bob" has received "Alice"'s key bundle
    When "Bob" verifies the signed pre-key
    Then "Bob" should check the signature using "Alice"'s identity key
    And the signature should be valid
    And session establishment should proceed

  Scenario: Reject invalid signed pre-key
    Given "Bob" has received a key bundle with tampered signed pre-key
    When "Bob" verifies the signed pre-key
    Then the signature verification should fail
    And session establishment should be aborted
    And an error should be logged

  Scenario: Secure key storage
    Given "Alice" has generated all required keys
    Then private keys should be encrypted at rest
    And encryption should use device-specific key
    And keys should be stored in secure enclave if available
    And memory containing keys should be cleared after use

  Scenario: Key backup and recovery
    Given "Alice" wants to backup her keys
    When "Alice" initiates key backup
    Then keys should be encrypted with recovery passphrase
    And the backup should use PBKDF2 with high iteration count
    And the backup should include all necessary keys
    But the backup should not include ephemeral keys

  Scenario: Emergency key deletion
    Given "Alice" suspects her device is compromised
    When "Alice" triggers remote wipe from another device
    Then all keys on the compromised device should be deleted
    And active sessions should be terminated
    And the device should be marked as revoked
    And new keys should be generated on other devices