import { Router } from 'express';
import { v4 as uuidv4 } from 'uuid';
import jwt from 'jsonwebtoken';
import { EncryptedMessage } from '@e2e-chat/shared';
import { messageDB, sessionDB } from '../services/database.js';
import { authMiddleware } from '../middleware/auth.js';

const router = Router();

router.use(authMiddleware);

router.post('/send', async (req, res) => {
  try {
    const { recipientId, ciphertext, nonce, authTag, ephemeralKey } = req.body;
    const senderId = (req as any).userId;

    // Check if session exists
    let session = await sessionDB.findByParticipants(senderId, recipientId);
    if (!session) {
      // Create new session
      session = await sessionDB.create({
        id: uuidv4(),
        participants: [senderId, recipientId],
        verified: false,
        createdAt: new Date()
      });
    }

    const message: EncryptedMessage = {
      id: uuidv4(),
      senderId,
      recipientId,
      ciphertext,
      nonce,
      authTag,
      ephemeralKey,
      timestamp: new Date()
    };

    const savedMessage = await messageDB.save(message);

    res.json({
      message: savedMessage,
      sessionId: session.id
    });
  } catch (error) {
    console.error('Send message error:', error);
    res.status(500).json({ error: 'Failed to send message' });
  }
});

router.get('/conversation/:userId', async (req, res) => {
  try {
    const currentUserId = (req as any).userId;
    const otherUserId = req.params.userId;

    const messages = await messageDB.getMessages(currentUserId, otherUserId);
    const session = await sessionDB.findByParticipants(currentUserId, otherUserId);

    res.json({
      messages,
      session
    });
  } catch (error) {
    console.error('Get messages error:', error);
    res.status(500).json({ error: 'Failed to get messages' });
  }
});

router.post('/verify-session', async (req, res) => {
  try {
    const { sessionId, securityNumber } = req.body;
    const userId = (req as any).userId;

    const session = await sessionDB.findById(sessionId);
    if (!session || !session.participants.includes(userId)) {
      return res.status(403).json({ error: 'Unauthorized' });
    }

    // In production, would verify the security number properly
    await sessionDB.updateVerified(sessionId, true);

    res.json({ verified: true });
  } catch (error) {
    console.error('Verify session error:', error);
    res.status(500).json({ error: 'Failed to verify session' });
  }
});

export { router as messagesRouter };