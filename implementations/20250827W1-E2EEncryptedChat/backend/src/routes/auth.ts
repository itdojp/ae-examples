import { Router } from 'express';
import bcrypt from 'bcryptjs';
import jwt from 'jsonwebtoken';
import { v4 as uuidv4 } from 'uuid';
import { User } from '@e2e-chat/shared';
import { userDB, keyDB } from '../services/database.js';
import { CryptoService } from '../services/crypto.js';

const router = Router();
const JWT_SECRET = process.env.JWT_SECRET || 'dev-secret-change-in-production';

router.post('/register', async (req, res) => {
  try {
    const { email, password, displayName } = req.body;

    // Check if user exists
    const existingUser = await userDB.findByEmail(email);
    if (existingUser) {
      return res.status(400).json({ error: 'User already exists' });
    }

    // Generate crypto keys
    const keyPair = CryptoService.generateKeyPair();
    const preKeys = CryptoService.generatePreKeys(100);

    // Hash password
    const passwordHash = await bcrypt.hash(password, 10);

    // Create user
    const user: User & { passwordHash: string; privateKey: string } = {
      id: uuidv4(),
      email,
      displayName,
      publicKey: keyPair.publicKey,
      privateKey: keyPair.privateKey,
      passwordHash,
      createdAt: new Date()
    };

    const savedUser = await userDB.create(user);
    await keyDB.savePublicKey(user.id, keyPair.publicKey);
    await keyDB.savePreKeys(user.id, preKeys);

    // Generate JWT
    const token = jwt.sign(
      { userId: user.id, email: user.email },
      JWT_SECRET,
      { expiresIn: '7d' }
    );

    res.json({
      token,
      user: savedUser,
      keyPair: {
        publicKey: keyPair.publicKey,
        privateKey: keyPair.privateKey
      },
      keyBundle: {
        identityKey: keyPair.publicKey,
        preKeys: preKeys.slice(0, 10) // Send first 10 pre-keys
      }
    });
  } catch (error) {
    console.error('Registration error:', error);
    res.status(500).json({ error: 'Registration failed' });
  }
});

router.post('/login', async (req, res) => {
  try {
    const { email, password } = req.body;

    // Find user
    const user = await userDB.findByEmail(email);
    if (!user) {
      return res.status(401).json({ error: 'Invalid credentials' });
    }

    // Check password
    const validPassword = await bcrypt.compare(password, user.passwordHash);
    if (!validPassword) {
      return res.status(401).json({ error: 'Invalid credentials' });
    }

    // Generate JWT
    const token = jwt.sign(
      { userId: user.id, email: user.email },
      JWT_SECRET,
      { expiresIn: '7d' }
    );

    const { passwordHash, privateKey, ...publicUser } = user;

    res.json({
      token,
      user: publicUser,
      keyPair: {
        publicKey: user.publicKey,
        privateKey: privateKey
      }
    });
  } catch (error) {
    console.error('Login error:', error);
    res.status(500).json({ error: 'Login failed' });
  }
});

router.get('/me', async (req, res) => {
  try {
    const authHeader = req.headers.authorization;
    if (!authHeader) {
      return res.status(401).json({ error: 'No token provided' });
    }

    const token = authHeader.replace('Bearer ', '');
    const decoded = jwt.verify(token, JWT_SECRET) as { userId: string };

    const user = await userDB.findById(decoded.userId);
    if (!user) {
      return res.status(404).json({ error: 'User not found' });
    }

    res.json({ user });
  } catch (error) {
    res.status(401).json({ error: 'Invalid token' });
  }
});

router.get('/users', async (req, res) => {
  try {
    const authHeader = req.headers.authorization;
    if (!authHeader) {
      return res.status(401).json({ error: 'No token provided' });
    }

    const token = authHeader.replace('Bearer ', '');
    const decoded = jwt.verify(token, JWT_SECRET) as { userId: string };

    const users = await userDB.getAllExcept(decoded.userId);
    res.json({ users });
  } catch (error) {
    res.status(500).json({ error: 'Failed to get users' });
  }
});

export { router as authRouter };