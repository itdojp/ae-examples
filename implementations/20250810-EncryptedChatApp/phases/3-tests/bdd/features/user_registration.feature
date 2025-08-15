Feature: User Registration and Authentication
  As a user
  I want to register and authenticate securely
  So that I can use the E2E encrypted chat service

  Background:
    Given the E2E chat system is initialized
    And cryptographic libraries are loaded

  Scenario: Successful user registration
    Given I am a new user
    When I register with email "alice@example.com", password "SecureP@ssw0rd123", and display name "Alice"
    Then my account should be created successfully
    And my identity key pair should be generated
    And my signed pre-key should be generated
    And 100 one-time pre-keys should be generated
    And I should receive a verification email

  Scenario: Registration with weak password
    Given I am a new user
    When I register with email "bob@example.com", password "weak", and display name "Bob"
    Then registration should fail with error "Password does not meet complexity requirements"

  Scenario: Registration with duplicate email
    Given a user exists with email "charlie@example.com"
    When I register with email "charlie@example.com", password "SecureP@ssw0rd456", and display name "Charlie2"
    Then registration should fail with error "Email already registered"

  Scenario: Successful login with 2FA
    Given I have a registered account with email "alice@example.com"
    And I have 2FA enabled
    When I login with email "alice@example.com", password "SecureP@ssw0rd123", and TOTP code "123456"
    Then I should be authenticated successfully
    And I should receive a JWT token
    And my device should be registered

  Scenario: Failed login with incorrect password
    Given I have a registered account with email "alice@example.com"
    When I login with email "alice@example.com" and password "WrongPassword"
    Then authentication should fail with error "Invalid credentials"

  Scenario: Failed login with incorrect 2FA code
    Given I have a registered account with email "alice@example.com"
    And I have 2FA enabled
    When I login with email "alice@example.com", password "SecureP@ssw0rd123", and TOTP code "000000"
    Then authentication should fail with error "Invalid 2FA code"

  Scenario: Enable two-factor authentication
    Given I am authenticated as "alice@example.com"
    When I enable 2FA
    Then a TOTP secret should be generated
    And backup codes should be generated
    And I should see a QR code for authenticator apps

  Scenario: Device trust management
    Given I am authenticated as "alice@example.com"
    And I have logged in from 3 different devices
    When I view my trusted devices
    Then I should see all 3 devices listed
    And I should be able to revoke access for any device