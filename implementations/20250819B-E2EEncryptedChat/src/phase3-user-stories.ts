/**
 * Phase 3: User Stories Creation
 * ユーザーストーリーの生成と管理
 */

import { UserStoriesTaskAdapter } from '../agents/user-stories-task-adapter';

export interface UserStory {
  id: string;
  epic: string;
  title: string;
  asA: string;
  iWant: string;
  soThat: string;
  acceptanceCriteria: AcceptanceCriterion[];
  priority: 'must' | 'should' | 'could' | 'wont';
  storyPoints: number;
  dependencies: string[];
  risks: string[];
  technicalNotes: string[];
}

export interface AcceptanceCriterion {
  given: string;
  when: string;
  then: string;
  and?: string[];
}

export class E2EChatUserStoriesGenerator {
  private storiesAdapter: UserStoriesTaskAdapter;

  constructor() {
    this.storiesAdapter = new UserStoriesTaskAdapter();
  }

  /**
   * エピック定義
   */
  defineEpics(): Map<string, string> {
    const epics = new Map<string, string>();
    
    epics.set('EPIC-001', 'User Authentication & Account Management');
    epics.set('EPIC-002', 'End-to-End Encryption Core');
    epics.set('EPIC-003', 'Secure Messaging');
    epics.set('EPIC-004', 'Key Management & Verification');
    epics.set('EPIC-005', 'Multi-Device Support');
    epics.set('EPIC-006', 'Privacy Controls');
    epics.set('EPIC-007', 'Group Chat (Future)');
    
    return epics;
  }

  /**
   * コアユーザーストーリー生成
   */
  generateCoreUserStories(): UserStory[] {
    return [
      {
        id: 'US-001',
        epic: 'EPIC-001',
        title: 'Secure Account Creation',
        asA: 'new user',
        iWant: 'to create an account with automatic encryption setup',
        soThat: 'I can start communicating securely immediately',
        acceptanceCriteria: [
          {
            given: 'I am on the registration page',
            when: 'I provide valid credentials',
            then: 'my encryption keys are generated automatically',
            and: [
              'keys are stored securely on my device',
              'public keys are uploaded to the server',
              'I receive a unique security code'
            ]
          }
        ],
        priority: 'must',
        storyPoints: 8,
        dependencies: [],
        risks: [
          'Key generation might fail on older devices',
          'Secure random number generation availability'
        ],
        technicalNotes: [
          'Use WebCrypto API for key generation',
          'Implement fallback to libsodium.js',
          'Keys must be generated client-side only'
        ]
      },
      {
        id: 'US-002',
        epic: 'EPIC-002',
        title: 'Automatic Message Encryption',
        asA: 'authenticated user',
        iWant: 'my messages to be encrypted automatically',
        soThat: 'I don\'t need to think about security',
        acceptanceCriteria: [
          {
            given: 'I am in a chat conversation',
            when: 'I send a message',
            then: 'it is encrypted before leaving my device',
            and: [
              'encryption happens in under 50ms',
              'no plaintext is ever sent to the server',
              'the UI shows encryption status'
            ]
          }
        ],
        priority: 'must',
        storyPoints: 13,
        dependencies: ['US-001'],
        risks: [
          'Performance impact on low-end devices',
          'Browser compatibility issues'
        ],
        technicalNotes: [
          'Implement Double Ratchet algorithm',
          'Use AES-256-GCM for message encryption',
          'Optimize for mobile devices'
        ]
      },
      {
        id: 'US-003',
        epic: 'EPIC-003',
        title: 'Real-time Secure Messaging',
        asA: 'user in a conversation',
        iWant: 'to send and receive messages in real-time',
        soThat: 'conversations feel natural and responsive',
        acceptanceCriteria: [
          {
            given: 'both users are online',
            when: 'a message is sent',
            then: 'it arrives within 200ms',
            and: [
              'delivery confirmation is shown',
              'messages appear in correct order',
              'typing indicators work (if enabled)'
            ]
          }
        ],
        priority: 'must',
        storyPoints: 8,
        dependencies: ['US-002'],
        risks: [
          'Network latency variations',
          'WebSocket connection stability'
        ],
        technicalNotes: [
          'Use WebSocket for real-time communication',
          'Implement message queuing for reliability',
          'Add exponential backoff for reconnection'
        ]
      },
      {
        id: 'US-004',
        epic: 'EPIC-004',
        title: 'Security Verification',
        asA: 'security-conscious user',
        iWant: 'to verify my contact\'s identity',
        soThat: 'I can prevent MITM attacks',
        acceptanceCriteria: [
          {
            given: 'I am chatting with a contact',
            when: 'I access verification options',
            then: 'I can verify via QR code or security number',
            and: [
              'verification status is clearly displayed',
              'verified chats show a badge',
              'I get alerts if keys change'
            ]
          }
        ],
        priority: 'should',
        storyPoints: 5,
        dependencies: ['US-002'],
        risks: [
          'Users might not understand verification',
          'QR code scanning compatibility'
        ],
        technicalNotes: [
          'Generate deterministic security numbers',
          'Implement QR code generation/scanning',
          'Store verification status locally'
        ]
      },
      {
        id: 'US-005',
        epic: 'EPIC-005',
        title: 'Multi-Device Message Sync',
        asA: 'user with multiple devices',
        iWant: 'my messages to sync across all devices',
        soThat: 'I can continue conversations anywhere',
        acceptanceCriteria: [
          {
            given: 'I have linked multiple devices',
            when: 'I send/receive a message on one device',
            then: 'it appears on all my devices',
            and: [
              'messages remain encrypted on all devices',
              'sync happens within 1 second',
              'message order is preserved'
            ]
          }
        ],
        priority: 'should',
        storyPoints: 13,
        dependencies: ['US-002', 'US-003'],
        risks: [
          'Key synchronization complexity',
          'Increased attack surface'
        ],
        technicalNotes: [
          'Implement Sesame protocol for device linking',
          'Use encrypted channels for key sharing',
          'Maintain separate ratchet state per device'
        ]
      },
      {
        id: 'US-006',
        epic: 'EPIC-006',
        title: 'Privacy Controls',
        asA: 'privacy-focused user',
        iWant: 'granular control over my privacy settings',
        soThat: 'I can customize my privacy level',
        acceptanceCriteria: [
          {
            given: 'I am in privacy settings',
            when: 'I modify privacy options',
            then: 'changes take effect immediately',
            and: [
              'I can disable read receipts',
              'I can disable typing indicators',
              'I can enable disappearing messages'
            ]
          }
        ],
        priority: 'should',
        storyPoints: 5,
        dependencies: ['US-003'],
        risks: [
          'Setting conflicts between users',
          'User confusion about settings impact'
        ],
        technicalNotes: [
          'Store settings locally and encrypted',
          'Implement setting negotiation protocol',
          'Ensure settings don\'t leak metadata'
        ]
      },
      {
        id: 'US-007',
        epic: 'EPIC-001',
        title: 'Two-Factor Authentication',
        asA: 'security-aware user',
        iWant: 'to enable 2FA on my account',
        soThat: 'my account is protected even if password is compromised',
        acceptanceCriteria: [
          {
            given: 'I am in account settings',
            when: 'I enable 2FA',
            then: 'I can choose TOTP or FIDO2',
            and: [
              'backup codes are generated',
              '2FA is required on new device login',
              'I can recover account with backup codes'
            ]
          }
        ],
        priority: 'must',
        storyPoints: 8,
        dependencies: ['US-001'],
        risks: [
          'User lockout if 2FA device is lost',
          'Recovery process security'
        ],
        technicalNotes: [
          'Implement TOTP with standard algorithm',
          'Support FIDO2/WebAuthn',
          'Secure backup code generation and storage'
        ]
      },
      {
        id: 'US-008',
        epic: 'EPIC-003',
        title: 'Offline Message Queue',
        asA: 'user with unstable connection',
        iWant: 'messages to be queued when offline',
        soThat: 'no messages are lost',
        acceptanceCriteria: [
          {
            given: 'I am offline',
            when: 'I send messages',
            then: 'they are queued locally',
            and: [
              'queued messages show pending status',
              'messages send automatically when online',
              'order is preserved'
            ]
          }
        ],
        priority: 'must',
        storyPoints: 5,
        dependencies: ['US-003'],
        risks: [
          'Queue corruption',
          'Storage limitations'
        ],
        technicalNotes: [
          'Use IndexedDB for message queue',
          'Implement retry logic with exponential backoff',
          'Handle queue overflow gracefully'
        ]
      }
    ];
  }

  /**
   * ストーリーポイント見積もり
   */
  estimateStoryPoints(story: UserStory): number {
    let points = 0;
    
    // 複雑度による基本ポイント
    const complexityFactors = {
      'encryption': 5,
      'real-time': 3,
      'multi-device': 5,
      'authentication': 3,
      'ui': 2
    };
    
    // Technical notesから複雑度を推定
    story.technicalNotes.forEach(note => {
      Object.keys(complexityFactors).forEach(factor => {
        if (note.toLowerCase().includes(factor)) {
          points += complexityFactors[factor];
        }
      });
    });
    
    // リスク要因による追加ポイント
    points += story.risks.length * 2;
    
    // 依存関係による追加ポイント
    points += story.dependencies.length;
    
    // フィボナッチ数列に正規化（1, 2, 3, 5, 8, 13, 21）
    const fibonacci = [1, 2, 3, 5, 8, 13, 21];
    return fibonacci.find(f => f >= points) || 21;
  }

  /**
   * スプリント計画
   */
  planSprints(stories: UserStory[], velocityPerSprint: number = 26): Map<number, UserStory[]> {
    const sprints = new Map<number, UserStory[]>();
    let currentSprint = 1;
    let currentVelocity = 0;
    let currentSprintStories: UserStory[] = [];
    
    // 優先度と依存関係でソート
    const sortedStories = this.topologicalSort(stories);
    
    for (const story of sortedStories) {
      if (currentVelocity + story.storyPoints > velocityPerSprint) {
        sprints.set(currentSprint, [...currentSprintStories]);
        currentSprint++;
        currentVelocity = 0;
        currentSprintStories = [];
      }
      
      currentSprintStories.push(story);
      currentVelocity += story.storyPoints;
    }
    
    if (currentSprintStories.length > 0) {
      sprints.set(currentSprint, currentSprintStories);
    }
    
    return sprints;
  }

  /**
   * トポロジカルソート（依存関係考慮）
   */
  private topologicalSort(stories: UserStory[]): UserStory[] {
    const sorted: UserStory[] = [];
    const visited = new Set<string>();
    const visiting = new Set<string>();
    
    const storyMap = new Map(stories.map(s => [s.id, s]));
    
    const visit = (storyId: string) => {
      if (visited.has(storyId)) return;
      if (visiting.has(storyId)) {
        throw new Error(`Circular dependency detected at ${storyId}`);
      }
      
      visiting.add(storyId);
      const story = storyMap.get(storyId);
      
      if (story) {
        for (const dep of story.dependencies) {
          if (storyMap.has(dep)) {
            visit(dep);
          }
        }
        sorted.push(story);
      }
      
      visiting.delete(storyId);
      visited.add(storyId);
    };
    
    // 優先度順にソート
    const priorityOrder = { 'must': 0, 'should': 1, 'could': 2, 'wont': 3 };
    const prioritySorted = [...stories].sort((a, b) => 
      priorityOrder[a.priority] - priorityOrder[b.priority]
    );
    
    for (const story of prioritySorted) {
      visit(story.id);
    }
    
    return sorted;
  }

  /**
   * テスト戦略生成
   */
  generateTestStrategy(stories: UserStory[]): Map<string, string[]> {
    const testStrategy = new Map<string, string[]>();
    
    for (const story of stories) {
      const tests: string[] = [];
      
      // Unit tests
      tests.push(`Unit: ${story.title} - Core logic`);
      
      // Integration tests
      if (story.dependencies.length > 0) {
        tests.push(`Integration: ${story.title} - Dependency integration`);
      }
      
      // E2E tests
      tests.push(`E2E: ${story.title} - Full user flow`);
      
      // Security tests
      if (story.epic.includes('002') || story.epic.includes('004')) {
        tests.push(`Security: ${story.title} - Penetration testing`);
        tests.push(`Security: ${story.title} - Cryptographic validation`);
      }
      
      // Performance tests
      if (story.technicalNotes.some(note => note.includes('performance') || note.includes('optimize'))) {
        tests.push(`Performance: ${story.title} - Load testing`);
        tests.push(`Performance: ${story.title} - Stress testing`);
      }
      
      testStrategy.set(story.id, tests);
    }
    
    return testStrategy;
  }
}

// Phase 3 実行
export async function executePhase3() {
  console.log('📋 Phase 3: User Stories Creation Starting...');
  
  const generator = new E2EChatUserStoriesGenerator();
  
  // 1. エピック定義
  const epics = generator.defineEpics();
  console.log(`✅ ${epics.size} Epics Defined`);
  
  // 2. ユーザーストーリー生成
  const stories = generator.generateCoreUserStories();
  console.log(`✅ ${stories.length} User Stories Generated`);
  
  // 3. スプリント計画
  const sprints = generator.planSprints(stories);
  console.log(`✅ ${sprints.size} Sprints Planned`);
  
  // 4. テスト戦略生成
  const testStrategy = generator.generateTestStrategy(stories);
  console.log('✅ Test Strategy Generated');
  
  // 5. Phase 3 成果物
  const phase3Output = {
    timestamp: new Date().toISOString(),
    epics: Array.from(epics.entries()),
    userStories: stories,
    totalStoryPoints: stories.reduce((sum, s) => sum + s.storyPoints, 0),
    sprintPlan: Array.from(sprints.entries()).map(([sprint, stories]) => ({
      sprint,
      stories: stories.map(s => s.id),
      totalPoints: stories.reduce((sum, s) => sum + s.storyPoints, 0)
    })),
    testStrategy: Array.from(testStrategy.entries()),
    nextPhase: 'Phase 4: Validation'
  };
  
  return phase3Output;
}