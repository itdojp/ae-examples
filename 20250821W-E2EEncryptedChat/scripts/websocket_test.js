import { WebSocket } from 'ws';

console.log('📡 WebSocket テストクライアントを開始します...\n');

const ws = new WebSocket('ws://localhost:3000/ws/read-status');

ws.on('open', function open() {
  console.log('✅ WebSocket接続が確立されました');
  
  // Ping テスト
  console.log('📤 Ping メッセージを送信中...');
  ws.send(JSON.stringify({
    type: 'ping'
  }));
  
  // 既読マークテスト
  setTimeout(() => {
    console.log('📤 既読マークメッセージを送信中...');
    ws.send(JSON.stringify({
      type: 'mark-read',
      messageId: 'websocket-test-message-001',
      deviceId: 'websocket-device-001'
    }));
  }, 1000);
  
  // 既読状況取得テスト
  setTimeout(() => {
    console.log('📤 既読状況取得メッセージを送信中...');
    ws.send(JSON.stringify({
      type: 'get-read-status',
      messageId: 'websocket-test-message-001'
    }));
  }, 2000);
  
  // 3秒後に接続終了
  setTimeout(() => {
    console.log('👋 WebSocket接続を終了します...');
    ws.close();
  }, 3000);
});

ws.on('message', function message(data) {
  const parsedData = JSON.parse(data.toString());
  console.log('📥 受信したメッセージ:', JSON.stringify(parsedData, null, 2));
});

ws.on('close', function close() {
  console.log('❌ WebSocket接続が終了しました');
});

ws.on('error', function error(err) {
  console.error('🚨 WebSocketエラー:', err.message);
});