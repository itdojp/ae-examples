import React, { useState } from 'react';
import { SecurityNumber } from '../domain/value-objects/SecurityNumber';
import QRCode from './QRCode';

interface SecurityVerificationProps {
  localNumber: SecurityNumber;
  onScan: (qrData: string) => void;
  onClose: () => void;
}

const SecurityVerification: React.FC<SecurityVerificationProps> = ({
  localNumber,
  onScan,
  onClose
}) => {
  const [scanMode, setScanMode] = useState(false);
  const [manualInput, setManualInput] = useState('');

  const handleManualVerify = () => {
    if (manualInput) {
      onScan(manualInput);
    }
  };

  return (
    <div className="modal-overlay" onClick={onClose}>
      <div className="modal-content" onClick={(e) => e.stopPropagation()}>
        <div className="modal-header">
          <h2>Verify Security Number</h2>
          <button className="close-button" onClick={onClose}>×</button>
        </div>
        
        <div className="modal-body">
          <div className="tabs">
            <button 
              className={`tab ${!scanMode ? 'active' : ''}`}
              onClick={() => setScanMode(false)}
            >
              Show QR Code
            </button>
            <button 
              className={`tab ${scanMode ? 'active' : ''}`}
              onClick={() => setScanMode(true)}
            >
              Scan QR Code
            </button>
          </div>
          
          {!scanMode ? (
            <div className="qr-display">
              <QRCode data={localNumber.toQRCode()} size={200} />
              <div className="security-number-display">
                <p className="instruction">
                  Or compare these numbers with your contact:
                </p>
                <pre className="number-text">{localNumber.toString()}</pre>
              </div>
            </div>
          ) : (
            <div className="qr-scan">
              <div className="scan-placeholder">
                <p>QR Scanner would be here</p>
                <p className="instruction">Or enter the security code manually:</p>
                <input
                  type="text"
                  className="manual-input"
                  placeholder="Enter security code..."
                  value={manualInput}
                  onChange={(e) => setManualInput(e.target.value)}
                />
                <button 
                  className="verify-button"
                  onClick={handleManualVerify}
                  disabled={!manualInput}
                >
                  Verify
                </button>
              </div>
            </div>
          )}
        </div>
        
        <style jsx>{`
          .modal-overlay {
            position: fixed;
            top: 0;
            left: 0;
            right: 0;
            bottom: 0;
            background: rgba(0, 0, 0, 0.5);
            display: flex;
            align-items: center;
            justify-content: center;
            z-index: 1000;
          }
          
          .modal-content {
            background: white;
            border-radius: 12px;
            width: 90%;
            max-width: 500px;
            box-shadow: 0 10px 40px rgba(0, 0, 0, 0.2);
          }
          
          .modal-header {
            display: flex;
            justify-content: space-between;
            align-items: center;
            padding: 20px;
            border-bottom: 1px solid #e0e0e0;
          }
          
          .modal-header h2 {
            margin: 0;
            font-size: 20px;
            color: #333;
          }
          
          .close-button {
            background: none;
            border: none;
            font-size: 28px;
            color: #999;
            cursor: pointer;
            padding: 0;
            width: 32px;
            height: 32px;
            display: flex;
            align-items: center;
            justify-content: center;
          }
          
          .close-button:hover {
            color: #666;
          }
          
          .modal-body {
            padding: 20px;
          }
          
          .tabs {
            display: flex;
            gap: 8px;
            margin-bottom: 24px;
          }
          
          .tab {
            flex: 1;
            padding: 10px;
            border: 1px solid #e0e0e0;
            background: white;
            cursor: pointer;
            border-radius: 8px;
            font-size: 14px;
            transition: all 0.2s;
          }
          
          .tab.active {
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            border-color: transparent;
          }
          
          .tab:not(.active):hover {
            background: #f5f5f5;
          }
          
          .qr-display {
            text-align: center;
          }
          
          .security-number-display {
            margin-top: 24px;
          }
          
          .instruction {
            color: #666;
            font-size: 14px;
            margin-bottom: 12px;
          }
          
          .number-text {
            background: #f5f5f5;
            padding: 16px;
            border-radius: 8px;
            font-family: 'Courier New', monospace;
            font-size: 14px;
            line-height: 1.6;
            color: #333;
          }
          
          .qr-scan {
            text-align: center;
          }
          
          .scan-placeholder {
            background: #f5f5f5;
            padding: 40px;
            border-radius: 8px;
            border: 2px dashed #ddd;
          }
          
          .manual-input {
            width: 100%;
            padding: 10px;
            margin-top: 16px;
            border: 1px solid #e0e0e0;
            border-radius: 8px;
            font-size: 14px;
          }
          
          .verify-button {
            margin-top: 16px;
            padding: 10px 24px;
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            border: none;
            border-radius: 8px;
            font-size: 14px;
            font-weight: 500;
            cursor: pointer;
            transition: opacity 0.2s;
          }
          
          .verify-button:hover:not(:disabled) {
            opacity: 0.9;
          }
          
          .verify-button:disabled {
            opacity: 0.5;
            cursor: not-allowed;
          }
        `}</style>
      </div>
    </div>
  );
};

export default SecurityVerification;