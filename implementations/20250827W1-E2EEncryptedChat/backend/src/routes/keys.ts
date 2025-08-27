import { Router } from 'express';
import { keyDB, userDB } from '../services/database.js';
import { authMiddleware } from '../middleware/auth.js';

const router = Router();

router.get('/:userId', async (req, res) => {
  try {
    const { userId } = req.params;

    const user = await userDB.findById(userId);
    if (!user) {
      return res.status(404).json({ error: 'User not found' });
    }

    const publicKey = await keyDB.getPublicKey(userId);
    const preKey = await keyDB.consumePreKey(userId);

    res.json({
      identityKey: publicKey,
      preKey: preKey || null
    });
  } catch (error) {
    console.error('Get keys error:', error);
    res.status(500).json({ error: 'Failed to get keys' });
  }
});

router.post('/rotate', authMiddleware, async (req, res) => {
  try {
    const userId = (req as any).userId;
    
    // In production, would generate new keys and update
    res.json({ rotated: true });
  } catch (error) {
    console.error('Rotate keys error:', error);
    res.status(500).json({ error: 'Failed to rotate keys' });
  }
});

export { router as keysRouter };