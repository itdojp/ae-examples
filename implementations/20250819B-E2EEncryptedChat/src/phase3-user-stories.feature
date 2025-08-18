# E2E Encrypted Chat User Stories
# BDD Specification using Gherkin syntax

Feature: User Registration and Key Generation
  As a new user
  I want to create a secure account with E2E encryption
  So that I can communicate privately

  Background:
    Given the E2E chat application is running
    And cryptographic libraries are initialized

  Scenario: Successful user registration with key generation
    Given I am on the registration page
    When I enter "user@example.com" as email
    And I enter "SecureP@ssw0rd123!" as password
    And I enter "Alice" as display name
    And I click the "Create Account" button
    Then I should see "Generating encryption keys..."
    And the system should generate an Ed25519 identity key pair
    And the system should generate a signed pre-key
    And the system should generate 100 one-time pre-keys
    And the keys should be encrypted and stored locally
    And I should see my unique security code
    And I should be redirected to the main chat interface

  Scenario: Password strength validation
    Given I am on the registration page
    When I enter "user@example.com" as email
    And I enter "weak" as password
    Then I should see "Password must be at least 12 characters"
    And I should see "Password must contain uppercase, lowercase, numbers, and symbols"
    And the "Create Account" button should be disabled

  Scenario: Duplicate email prevention
    Given a user with email "existing@example.com" already exists
    When I try to register with email "existing@example.com"
    Then I should see "An account with this email already exists"
    And registration should be prevented

Feature: Secure Message Exchange
  As an authenticated user
  I want to send and receive encrypted messages
  So that my communications remain private

  Background:
    Given I am logged in as "Alice"
    And "Bob" is a registered user
    And we have established a secure session

  Scenario: Sending an encrypted text message
    Given I am in a chat with "Bob"
    When I type "Hello, this is a secure message!"
    And I press the send button
    Then the system should:
      | Step | Action                                    |
      | 1    | Derive message key using Double Ratchet  |
      | 2    | Encrypt message with AES-256-GCM         |
      | 3    | Generate authentication tag               |
      | 4    | Send encrypted payload to server         |
      | 5    | Destroy message key immediately          |
    And "Bob" should receive the encrypted message
    And only "Bob" should be able to decrypt it
    And the message should appear in my chat as "sent"

  Scenario: Receiving and decrypting a message
    Given "Bob" has sent me an encrypted message
    When the message arrives at my device
    Then the system should:
      | Step | Action                                    |
      | 1    | Verify message authentication tag        |
      | 2    | Derive decryption key using Double Ratchet |
      | 3    | Decrypt message with AES-256-GCM         |
      | 4    | Display plaintext message                |
      | 5    | Update ratchet state                     |
    And I should see the decrypted message content
    And the encryption indicator should show "🔒 Encrypted"

  Scenario: Perfect Forward Secrecy verification
    Given I have exchanged 10 messages with "Bob"
    When the current session key is compromised
    Then previous messages should remain encrypted
    And an attacker should not be able to decrypt past messages
    And future messages should use new keys

Feature: Security Verification
  As a security-conscious user
  I want to verify the identity of my chat partners
  So that I can prevent man-in-the-middle attacks

  Background:
    Given I am logged in as "Alice"
    And I have an active chat with "Bob"

  Scenario: QR code verification in person
    Given "Bob" and I are in the same physical location
    When I open the security verification screen
    Then I should see my QR code containing our security numbers
    When "Bob" scans my QR code with his device
    And his security number matches mine
    Then our chat should be marked as "Verified ✓"
    And a verification event should be logged
    And future messages should show the verified badge

  Scenario: Manual security number comparison
    Given I am on a voice call with "Bob"
    When I open the security verification screen
    Then I should see a 60-digit security number
    When I read my security number to "Bob"
    And "Bob" confirms his number matches
    And I mark the conversation as verified
    Then our chat should be marked as "Verified ✓"

  Scenario: Security number change detection
    Given my chat with "Bob" is verified
    When "Bob"'s encryption keys change
    Then I should see a warning "Security number has changed"
    And the verified status should be removed
    And I should be prompted to re-verify

Feature: Multi-Device Synchronization
  As a user with multiple devices
  I want my encrypted messages to sync across all my devices
  So that I can seamlessly continue conversations

  Background:
    Given I am logged in on my primary device
    And E2E encryption is active

  Scenario: Adding a new device
    When I log in on a new device
    Then I should see "Link this device to your account"
    When I scan the QR code from my primary device
    Then the new device should:
      | Step | Action                                    |
      | 1    | Establish secure channel with primary    |
      | 2    | Receive encrypted key bundle             |
      | 3    | Decrypt and store keys locally           |
      | 4    | Sync recent message history              |
      | 5    | Register for future message delivery     |
    And I should see my existing conversations
    And all messages should remain encrypted

  Scenario: Message sync across devices
    Given I have 2 linked devices
    When I send a message from Device A
    Then Device B should receive the message within 1 second
    And the message should be encrypted on both devices
    And both devices should maintain consistent ratchet state

  Scenario: Device revocation
    Given I have 3 linked devices
    When I revoke access for Device 2
    Then Device 2 should be immediately logged out
    And Device 2 should not receive new messages
    And encryption keys should be rotated
    And remaining devices should continue to work

Feature: Offline Message Handling
  As a user with intermittent connectivity
  I want messages to be queued when offline
  So that no messages are lost

  Scenario: Sending messages while offline
    Given I am in a chat with "Bob"
    And my device is offline
    When I send 3 messages
    Then the messages should be queued locally
    And marked with "pending" status
    When my device comes back online
    Then the messages should be encrypted and sent in order
    And their status should update to "sent"

  Scenario: Receiving messages while offline
    Given "Bob" sends me 5 messages while I'm offline
    When I come back online
    Then I should receive all 5 messages in order
    And they should be decrypted correctly
    And no messages should be lost or duplicated

Feature: Group Chat Encryption (Future)
  As a team member
  I want to have encrypted group conversations
  So that team communications remain private

  @future
  Scenario: Creating an encrypted group chat
    Given I want to create a group chat
    When I add "Bob", "Carol", and "Dave" to the group
    And I name the group "Secret Project"
    Then the system should:
      | Step | Action                                    |
      | 1    | Generate group encryption key            |
      | 2    | Encrypt group key for each member        |
      | 3    | Distribute encrypted keys to members     |
      | 4    | Establish group ratchet state           |
    And all members should be able to decrypt group messages
    And non-members should not be able to decrypt messages

  @future
  Scenario: Member removal from group
    Given I am admin of group "Secret Project"
    When I remove "Dave" from the group
    Then the system should:
      | Step | Action                                    |
      | 1    | Generate new group key                   |
      | 2    | Distribute to remaining members          |
      | 3    | Prevent Dave from decrypting new messages |
      | 4    | Maintain history for remaining members   |

Feature: Privacy Settings
  As a privacy-conscious user
  I want to control my privacy settings
  So that I can manage what information is shared

  Scenario: Disabling read receipts
    Given I am in settings
    When I disable "Read Receipts"
    Then other users should not see when I've read their messages
    But I should still see when others read my messages if they allow it

  Scenario: Disabling typing indicators
    Given I am in settings
    When I disable "Typing Indicators"
    Then other users should not see when I'm typing
    But I should still see when others are typing if they allow it

  Scenario: Message disappearing timer
    Given I am in a chat with "Bob"
    When I enable disappearing messages with 24 hour timer
    Then new messages should auto-delete after 24 hours
    And both devices should honor the timer
    And deleted messages should be unrecoverable