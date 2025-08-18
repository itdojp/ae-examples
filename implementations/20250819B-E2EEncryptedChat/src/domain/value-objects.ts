/**
 * Domain Value Objects for E2E Encrypted Chat Application - Phase 5
 * 
 * This file contains immutable value objects following DDD principles.
 * Value objects are defined by their attributes rather than identity.
 */

/**
 * Base interface for value objects with equality comparison
 */
interface ValueObject<T> {
  equals(other: T): boolean;
  readonly value: string | number | ArrayBuffer;
}

/**
 * Unique identifier for users in the system
 */
export class UserId implements ValueObject<UserId> {
  private constructor(private readonly _value: string) {
    if (!this.isValidUuid(_value)) {
      throw new Error('UserId must be a valid UUID');
    }
  }

  static create(value: string): UserId {
    return new UserId(value);
  }

  static generate(): UserId {
    return new UserId(this.generateUuid());
  }

  get value(): string {
    return this._value;
  }

  equals(other: UserId): boolean {
    return this._value === other._value;
  }

  toString(): string {
    return this._value;
  }

  private isValidUuid(uuid: string): boolean {
    const uuidRegex = /^[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i;
    return uuidRegex.test(uuid);
  }

  private static generateUuid(): string {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, (c) => {
      const r = Math.random() * 16 | 0;
      const v = c === 'x' ? r : (r & 0x3 | 0x8);
      return v.toString(16);
    });
  }
}

/**
 * Email address value object with validation
 */
export class Email implements ValueObject<Email> {
  private constructor(private readonly _value: string) {
    if (!this.isValidEmail(_value)) {
      throw new Error('Invalid email format');
    }
  }

  static create(value: string): Email {
    return new Email(value.toLowerCase().trim());
  }

  get value(): string {
    return this._value;
  }

  get domain(): string {
    return this._value.split('@')[1];
  }

  get localPart(): string {
    return this._value.split('@')[0];
  }

  equals(other: Email): boolean {
    return this._value === other._value;
  }

  toString(): string {
    return this._value;
  }

  private isValidEmail(email: string): boolean {
    const emailRegex = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
    return emailRegex.test(email) && email.length <= 254;
  }
}

/**
 * Secure password value object with validation
 */
export class Password {
  private constructor(private readonly _hashedValue: string) {}

  static create(plaintext: string): Password {
    if (!this.isValidPassword(plaintext)) {
      throw new Error('Password does not meet security requirements');
    }
    
    // In a real implementation, this would use a proper hashing library like bcrypt
    const hashedValue = this.hash(plaintext);
    return new Password(hashedValue);
  }

  static fromHash(hashedValue: string): Password {
    if (hashedValue.length === 0) {
      throw new Error('Hashed password cannot be empty');
    }
    return new Password(hashedValue);
  }

  verify(plaintext: string): boolean {
    // In a real implementation, this would use proper password verification
    return this.hash(plaintext) === this._hashedValue;
  }

  get hashedValue(): string {
    return this._hashedValue;
  }

  private static isValidPassword(password: string): boolean {
    // Minimum 8 characters, at least one uppercase, one lowercase, one digit, one special char
    const minLength = password.length >= 8;
    const hasUppercase = /[A-Z]/.test(password);
    const hasLowercase = /[a-z]/.test(password);
    const hasDigit = /\d/.test(password);
    const hasSpecialChar = /[!@#$%^&*(),.?":{}|<>]/.test(password);
    
    return minLength && hasUppercase && hasLowercase && hasDigit && hasSpecialChar;
  }

  private static hash(password: string): string {
    // This is a simplified hash for demonstration. In production, use bcrypt or similar
    let hash = 0;
    for (let i = 0; i < password.length; i++) {
      const char = password.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash = hash & hash; // Convert to 32-bit integer
    }
    return hash.toString(36);
  }
}

/**
 * Encrypted data with authentication tag
 */
export class CipherText implements ValueObject<CipherText> {
  private constructor(private readonly _value: ArrayBuffer) {
    if (_value.byteLength === 0) {
      throw new Error('CipherText cannot be empty');
    }
  }

  static create(value: ArrayBuffer): CipherText {
    return new CipherText(value.slice()); // Create a copy
  }

  static fromBase64(base64: string): CipherText {
    try {
      const binaryString = atob(base64);
      const bytes = new Uint8Array(binaryString.length);
      for (let i = 0; i < binaryString.length; i++) {
        bytes[i] = binaryString.charCodeAt(i);
      }
      return new CipherText(bytes.buffer);
    } catch (error) {
      throw new Error('Invalid base64 ciphertext');
    }
  }

  get value(): ArrayBuffer {
    return this._value.slice(); // Return a copy to maintain immutability
  }

  get length(): number {
    return this._value.byteLength;
  }

  toBase64(): string {
    const bytes = new Uint8Array(this._value);
    let binaryString = '';
    for (let i = 0; i < bytes.length; i++) {
      binaryString += String.fromCharCode(bytes[i]);
    }
    return btoa(binaryString);
  }

  equals(other: CipherText): boolean {
    if (this._value.byteLength !== other._value.byteLength) {
      return false;
    }
    const thisView = new Uint8Array(this._value);
    const otherView = new Uint8Array(other._value);
    for (let i = 0; i < thisView.length; i++) {
      if (thisView[i] !== otherView[i]) {
        return false;
      }
    }
    return true;
  }
}

/**
 * Cryptographic nonce for encryption
 */
export class Nonce implements ValueObject<Nonce> {
  private static readonly NONCE_LENGTH = 12; // 96 bits for AES-GCM

  private constructor(private readonly _value: ArrayBuffer) {
    if (_value.byteLength !== Nonce.NONCE_LENGTH) {
      throw new Error(`Nonce must be exactly ${Nonce.NONCE_LENGTH} bytes`);
    }
  }

  static create(value: ArrayBuffer): Nonce {
    return new Nonce(value.slice());
  }

  static generate(): Nonce {
    const nonce = new Uint8Array(Nonce.NONCE_LENGTH);
    crypto.getRandomValues(nonce);
    return new Nonce(nonce.buffer);
  }

  static fromBase64(base64: string): Nonce {
    try {
      const binaryString = atob(base64);
      if (binaryString.length !== Nonce.NONCE_LENGTH) {
        throw new Error(`Nonce must be exactly ${Nonce.NONCE_LENGTH} bytes`);
      }
      const bytes = new Uint8Array(binaryString.length);
      for (let i = 0; i < binaryString.length; i++) {
        bytes[i] = binaryString.charCodeAt(i);
      }
      return new Nonce(bytes.buffer);
    } catch (error) {
      throw new Error('Invalid base64 nonce');
    }
  }

  get value(): ArrayBuffer {
    return this._value.slice();
  }

  toBase64(): string {
    const bytes = new Uint8Array(this._value);
    let binaryString = '';
    for (let i = 0; i < bytes.length; i++) {
      binaryString += String.fromCharCode(bytes[i]);
    }
    return btoa(binaryString);
  }

  equals(other: Nonce): boolean {
    const thisView = new Uint8Array(this._value);
    const otherView = new Uint8Array(other._value);
    for (let i = 0; i < thisView.length; i++) {
      if (thisView[i] !== otherView[i]) {
        return false;
      }
    }
    return true;
  }
}

/**
 * Authentication tag for message integrity
 */
export class AuthenticationTag implements ValueObject<AuthenticationTag> {
  private static readonly TAG_LENGTH = 16; // 128 bits for AES-GCM

  private constructor(private readonly _value: ArrayBuffer) {
    if (_value.byteLength !== AuthenticationTag.TAG_LENGTH) {
      throw new Error(`Authentication tag must be exactly ${AuthenticationTag.TAG_LENGTH} bytes`);
    }
  }

  static create(value: ArrayBuffer): AuthenticationTag {
    return new AuthenticationTag(value.slice());
  }

  static fromBase64(base64: string): AuthenticationTag {
    try {
      const binaryString = atob(base64);
      if (binaryString.length !== AuthenticationTag.TAG_LENGTH) {
        throw new Error(`Authentication tag must be exactly ${AuthenticationTag.TAG_LENGTH} bytes`);
      }
      const bytes = new Uint8Array(binaryString.length);
      for (let i = 0; i < binaryString.length; i++) {
        bytes[i] = binaryString.charCodeAt(i);
      }
      return new AuthenticationTag(bytes.buffer);
    } catch (error) {
      throw new Error('Invalid base64 authentication tag');
    }
  }

  get value(): ArrayBuffer {
    return this._value.slice();
  }

  toBase64(): string {
    const bytes = new Uint8Array(this._value);
    let binaryString = '';
    for (let i = 0; i < bytes.length; i++) {
      binaryString += String.fromCharCode(bytes[i]);
    }
    return btoa(binaryString);
  }

  equals(other: AuthenticationTag): boolean {
    const thisView = new Uint8Array(this._value);
    const otherView = new Uint8Array(other._value);
    for (let i = 0; i < thisView.length; i++) {
      if (thisView[i] !== otherView[i]) {
        return false;
      }
    }
    return true;
  }
}

/**
 * Security number for verification between users
 */
export class SecurityNumber implements ValueObject<SecurityNumber> {
  private static readonly SECURITY_NUMBER_LENGTH = 60; // 12 groups of 5 digits

  private constructor(private readonly _value: string) {
    if (!this.isValidSecurityNumber(_value)) {
      throw new Error('Security number must be 60 digits in groups of 5');
    }
  }

  static create(value: string): SecurityNumber {
    // Remove spaces and format as groups of 5
    const cleanValue = value.replace(/\s/g, '');
    if (cleanValue.length !== SecurityNumber.SECURITY_NUMBER_LENGTH) {
      throw new Error(`Security number must be exactly ${SecurityNumber.SECURITY_NUMBER_LENGTH} digits`);
    }
    const formatted = cleanValue.match(/.{1,5}/g)?.join(' ') || '';
    return new SecurityNumber(formatted);
  }

  static generate(): SecurityNumber {
    let digits = '';
    for (let i = 0; i < SecurityNumber.SECURITY_NUMBER_LENGTH; i++) {
      digits += Math.floor(Math.random() * 10);
    }
    return SecurityNumber.create(digits);
  }

  get value(): string {
    return this._value;
  }

  get rawValue(): string {
    return this._value.replace(/\s/g, '');
  }

  equals(other: SecurityNumber): boolean {
    return this._value === other._value;
  }

  toString(): string {
    return this._value;
  }

  private isValidSecurityNumber(value: string): boolean {
    // Should be 60 digits formatted as groups of 5 separated by spaces
    const pattern = /^(\d{5}\s){11}\d{5}$/;
    return pattern.test(value);
  }
}

/**
 * Unique message identifier
 */
export class MessageId implements ValueObject<MessageId> {
  private constructor(private readonly _value: string) {
    if (!this.isValidUuid(_value)) {
      throw new Error('MessageId must be a valid UUID');
    }
  }

  static create(value: string): MessageId {
    return new MessageId(value);
  }

  static generate(): MessageId {
    return new MessageId(this.generateUuid());
  }

  get value(): string {
    return this._value;
  }

  equals(other: MessageId): boolean {
    return this._value === other._value;
  }

  toString(): string {
    return this._value;
  }

  private isValidUuid(uuid: string): boolean {
    const uuidRegex = /^[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i;
    return uuidRegex.test(uuid);
  }

  private static generateUuid(): string {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, (c) => {
      const r = Math.random() * 16 | 0;
      const v = c === 'x' ? r : (r & 0x3 | 0x8);
      return v.toString(16);
    });
  }
}

/**
 * Unique session identifier
 */
export class SessionId implements ValueObject<SessionId> {
  private constructor(private readonly _value: string) {
    if (!this.isValidUuid(_value)) {
      throw new Error('SessionId must be a valid UUID');
    }
  }

  static create(value: string): SessionId {
    return new SessionId(value);
  }

  static generate(): SessionId {
    return new SessionId(this.generateUuid());
  }

  get value(): string {
    return this._value;
  }

  equals(other: SessionId): boolean {
    return this._value === other._value;
  }

  toString(): string {
    return this._value;
  }

  private isValidUuid(uuid: string): boolean {
    const uuidRegex = /^[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i;
    return uuidRegex.test(uuid);
  }

  private static generateUuid(): string {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, (c) => {
      const r = Math.random() * 16 | 0;
      const v = c === 'x' ? r : (r & 0x3 | 0x8);
      return v.toString(16);
    });
  }
}

/**
 * Unique device identifier
 */
export class DeviceId implements ValueObject<DeviceId> {
  private constructor(private readonly _value: string) {
    if (!this.isValidUuid(_value)) {
      throw new Error('DeviceId must be a valid UUID');
    }
  }

  static create(value: string): DeviceId {
    return new DeviceId(value);
  }

  static generate(): DeviceId {
    return new DeviceId(this.generateUuid());
  }

  get value(): string {
    return this._value;
  }

  equals(other: DeviceId): boolean {
    return this._value === other._value;
  }

  toString(): string {
    return this._value;
  }

  private isValidUuid(uuid: string): boolean {
    const uuidRegex = /^[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i;
    return uuidRegex.test(uuid);
  }

  private static generateUuid(): string {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, (c) => {
      const r = Math.random() * 16 | 0;
      const v = c === 'x' ? r : (r & 0x3 | 0x8);
      return v.toString(16);
    });
  }
}

/**
 * Immutable timestamp with validation and comparison methods
 */
export class Timestamp implements ValueObject<Timestamp> {
  private constructor(private readonly _value: number) {
    if (!this.isValidTimestamp(_value)) {
      throw new Error('Invalid timestamp value');
    }
  }

  static create(value: number): Timestamp {
    return new Timestamp(value);
  }

  static now(): Timestamp {
    return new Timestamp(Date.now());
  }

  static fromDate(date: Date): Timestamp {
    return new Timestamp(date.getTime());
  }

  static fromISOString(isoString: string): Timestamp {
    const date = new Date(isoString);
    if (isNaN(date.getTime())) {
      throw new Error('Invalid ISO string for timestamp');
    }
    return new Timestamp(date.getTime());
  }

  get value(): number {
    return this._value;
  }

  toDate(): Date {
    return new Date(this._value);
  }

  toISOString(): string {
    return this.toDate().toISOString();
  }

  equals(other: Timestamp): boolean {
    return this._value === other._value;
  }

  isBefore(other: Timestamp): boolean {
    return this._value < other._value;
  }

  isAfter(other: Timestamp): boolean {
    return this._value > other._value;
  }

  isWithin(duration: number, other: Timestamp): boolean {
    return Math.abs(this._value - other._value) <= duration;
  }

  addMilliseconds(ms: number): Timestamp {
    return new Timestamp(this._value + ms);
  }

  subtractMilliseconds(ms: number): Timestamp {
    return new Timestamp(this._value - ms);
  }

  differenceInMilliseconds(other: Timestamp): number {
    return this._value - other._value;
  }

  toString(): string {
    return this.toISOString();
  }

  private isValidTimestamp(value: number): boolean {
    return Number.isInteger(value) && 
           value >= 0 && 
           value <= 8640000000000000; // Max timestamp value
  }
}