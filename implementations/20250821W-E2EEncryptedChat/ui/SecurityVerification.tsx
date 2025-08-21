'use client';

import React, { useState, useEffect, useCallback, useRef } from 'react';
import { Button } from '@ae-framework/ui/components/button';
import { Dialog } from '@ae-framework/ui/components/dialog';
import { Input } from '@ae-framework/ui/components/input';
import {
  QrCode,
  Scan,
  Shield,
  ShieldCheck,
  ShieldAlert,
  AlertTriangle,
  Copy,
  CheckCircle,
  Camera,
  Upload,
  X,
  RefreshCw,
  Eye,
  EyeOff
} from 'lucide-react';

// Types
interface SecurityNumber {
  digits: string;
  formatted: string;
}

interface VerificationData {
  qrCode: string;
  securityNumber: SecurityNumber;
  userPublicKey: string;
  otherUserPublicKey: string;
  verificationHash: string;
}

interface SecurityVerificationProps {
  isOpen: boolean;
  onClose: () => void;
  verificationData: VerificationData;
  otherUserName: string;
  onVerify: (verified: boolean) => Promise<void>;
  onKeyChange?: (reason: string) => void;
  hasKeyChanged?: boolean;
  className?: string;
}

interface QRCodeScannerProps {
  onScan: (data: string) => void;
  onError: (error: string) => void;
  isActive: boolean;
}

interface SecurityNumberDisplayProps {
  securityNumber: SecurityNumber;
  otherUserName: string;
  onCopy: () => void;
  showNumbers: boolean;
  onToggleVisibility: () => void;
}

// Mock QR Code Scanner Component (in a real implementation, use react-qr-scanner or similar)
const QRCodeScanner: React.FC<QRCodeScannerProps> = ({
  onScan,
  onError,
  isActive
}) => {
  const [isScanning, setIsScanning] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const fileInputRef = useRef<HTMLInputElement>(null);

  const handleFileUpload = useCallback((event: React.ChangeEvent<HTMLInputElement>) => {
    const file = event.target.files?.[0];
    if (!file) return;

    // In a real implementation, use a QR code reader library
    // For now, simulate scanning
    setTimeout(() => {
      const mockQrData = `verification:${Date.now()}`;
      onScan(mockQrData);
    }, 1000);

    setIsScanning(true);
    setTimeout(() => setIsScanning(false), 1000);
  }, [onScan]);

  const startCamera = useCallback(() => {
    setIsScanning(true);
    setError(null);
    
    // Simulate camera access
    setTimeout(() => {
      try {
        // Mock successful scan
        const mockQrData = `verification:${Date.now()}`;
        onScan(mockQrData);
        setIsScanning(false);
      } catch (err) {
        setError('Camera access denied');
        onError('Camera access denied');
        setIsScanning(false);
      }
    }, 2000);
  }, [onScan, onError]);

  if (!isActive) return null;

  return (
    <div className="space-y-4">
      <div className="relative bg-gray-900 rounded-lg overflow-hidden aspect-square">
        {isScanning ? (
          <div className="flex items-center justify-center h-full">
            <div className="text-center text-white">
              <RefreshCw className="w-8 h-8 animate-spin mx-auto mb-2" />
              <p>Scanning for QR code...</p>
            </div>
          </div>
        ) : (
          <div className="flex items-center justify-center h-full bg-gray-800">
            <div className="text-center text-gray-400">
              <Camera className="w-12 h-12 mx-auto mb-2" />
              <p>Camera preview will appear here</p>
            </div>
          </div>
        )}
        
        {/* Scanning overlay */}
        {isScanning && (
          <div className="absolute inset-0 border-4 border-blue-500 animate-pulse rounded-lg" />
        )}
      </div>

      {error && (
        <div className="flex items-center gap-2 p-3 bg-red-100 text-red-700 rounded-lg">
          <AlertTriangle className="w-4 h-4" />
          <span className="text-sm">{error}</span>
        </div>
      )}

      <div className="flex gap-2">
        <Button
          onClick={startCamera}
          disabled={isScanning}
          className="flex-1"
        >
          <Camera className="w-4 h-4 mr-2" />
          {isScanning ? 'Scanning...' : 'Start Camera'}
        </Button>
        
        <Button
          variant="outline"
          onClick={() => fileInputRef.current?.click()}
          disabled={isScanning}
        >
          <Upload className="w-4 h-4 mr-2" />
          Upload QR
        </Button>
      </div>

      <input
        ref={fileInputRef}
        type="file"
        accept="image/*"
        onChange={handleFileUpload}
        className="hidden"
        aria-label="Upload QR code image"
      />
    </div>
  );
};

// Security Number Display Component
const SecurityNumberDisplay: React.FC<SecurityNumberDisplayProps> = ({
  securityNumber,
  otherUserName,
  onCopy,
  showNumbers,
  onToggleVisibility
}) => {
  const [copied, setCopied] = useState(false);

  const handleCopy = useCallback(async () => {
    try {
      await navigator.clipboard.writeText(securityNumber.digits);
      setCopied(true);
      onCopy();
      setTimeout(() => setCopied(false), 2000);
    } catch (error) {
      console.error('Failed to copy security number:', error);
    }
  }, [securityNumber.digits, onCopy]);

  return (
    <div className="space-y-4">
      <div className="text-center">
        <h3 className="text-lg font-semibold text-gray-900 mb-2">
          Security Numbers
        </h3>
        <p className="text-sm text-gray-600">
          Compare these numbers with {otherUserName} to verify your connection is secure.
        </p>
      </div>

      <div className="bg-gray-50 rounded-lg p-4 space-y-3">
        <div className="flex items-center justify-between">
          <span className="text-sm font-medium text-gray-700">Your numbers:</span>
          <div className="flex items-center gap-2">
            <Button
              variant="ghost"
              size="sm"
              onClick={onToggleVisibility}
              aria-label={showNumbers ? 'Hide numbers' : 'Show numbers'}
            >
              {showNumbers ? <EyeOff className="w-4 h-4" /> : <Eye className="w-4 h-4" />}
            </Button>
            <Button
              variant="ghost"
              size="sm"
              onClick={handleCopy}
              disabled={!showNumbers}
              aria-label="Copy security numbers"
            >
              {copied ? <CheckCircle className="w-4 h-4 text-green-600" /> : <Copy className="w-4 h-4" />}
            </Button>
          </div>
        </div>
        
        <div className="font-mono text-center text-lg tracking-wider p-3 bg-white rounded border-2 border-dashed border-gray-300">
          {showNumbers ? securityNumber.formatted : '••• ••• ••• •••'}
        </div>
        
        <p className="text-xs text-center text-gray-500">
          {showNumbers && 'These numbers should match exactly with your contact'}
        </p>
      </div>
    </div>
  );
};

// Key Change Warning Component
const KeyChangeWarning: React.FC<{
  otherUserName: string;
  onAccept: () => void;
  onReject: () => void;
}> = ({ otherUserName, onAccept, onReject }) => {
  return (
    <div className="space-y-4">
      <div className="flex items-start gap-3 p-4 bg-red-50 border border-red-200 rounded-lg">
        <ShieldAlert className="w-6 h-6 text-red-600 flex-shrink-0 mt-0.5" />
        <div className="space-y-2">
          <h3 className="font-semibold text-red-900">
            Security keys have changed
          </h3>
          <p className="text-sm text-red-800">
            {otherUserName}'s security key has changed. This could mean:
          </p>
          <ul className="text-sm text-red-800 list-disc list-inside space-y-1 ml-2">
            <li>They reinstalled the app</li>
            <li>They're using a new device</li>
            <li>Someone is trying to intercept your messages</li>
          </ul>
          <p className="text-sm font-medium text-red-900">
            Only accept if you trust this change.
          </p>
        </div>
      </div>

      <div className="flex gap-3">
        <Button
          variant="destructive"
          onClick={onReject}
          className="flex-1"
        >
          <X className="w-4 h-4 mr-2" />
          Reject & Block
        </Button>
        <Button
          variant="outline"
          onClick={onAccept}
          className="flex-1"
        >
          <CheckCircle className="w-4 h-4 mr-2" />
          Accept Change
        </Button>
      </div>
    </div>
  );
};

// Main Security Verification Component
export const SecurityVerification: React.FC<SecurityVerificationProps> = ({
  isOpen,
  onClose,
  verificationData,
  otherUserName,
  onVerify,
  onKeyChange,
  hasKeyChanged = false,
  className = ''
}) => {
  const [currentStep, setCurrentStep] = useState<'overview' | 'qr' | 'numbers' | 'scan'>('overview');
  const [showNumbers, setShowNumbers] = useState(false);
  const [isVerifying, setIsVerifying] = useState(false);
  const [verificationResult, setVerificationResult] = useState<'success' | 'failed' | null>(null);

  const handleQRScan = useCallback(async (data: string) => {
    setIsVerifying(true);
    
    try {
      // In a real implementation, validate the scanned QR data
      const isValid = data.includes('verification:');
      
      setTimeout(() => {
        setVerificationResult(isValid ? 'success' : 'failed');
        setIsVerifying(false);
        
        if (isValid) {
          setTimeout(() => {
            onVerify(true);
            onClose();
          }, 1500);
        }
      }, 1000);
    } catch (error) {
      console.error('Verification failed:', error);
      setVerificationResult('failed');
      setIsVerifying(false);
    }
  }, [onVerify, onClose]);

  const handleManualVerification = useCallback(async (verified: boolean) => {
    setIsVerifying(true);
    
    try {
      await onVerify(verified);
      setVerificationResult(verified ? 'success' : 'failed');
      
      if (verified) {
        setTimeout(() => {
          onClose();
        }, 1500);
      }
    } catch (error) {
      console.error('Verification failed:', error);
      setVerificationResult('failed');
    } finally {
      setIsVerifying(false);
    }
  }, [onVerify, onClose]);

  const handleKeyChangeAccept = useCallback(() => {
    onKeyChange?.('accepted');
    setCurrentStep('overview');
  }, [onKeyChange]);

  const handleKeyChangeReject = useCallback(() => {
    onKeyChange?.('rejected');
    onClose();
  }, [onKeyChange, onClose]);

  const handleCopyNumbers = useCallback(() => {
    // Analytics or tracking could be added here
    console.log('Security numbers copied');
  }, []);

  const renderStepContent = () => {
    if (hasKeyChanged) {
      return (
        <KeyChangeWarning
          otherUserName={otherUserName}
          onAccept={handleKeyChangeAccept}
          onReject={handleKeyChangeReject}
        />
      );
    }

    if (verificationResult) {
      return (
        <div className="text-center space-y-4">
          <div className={`w-16 h-16 mx-auto rounded-full flex items-center justify-center ${
            verificationResult === 'success' ? 'bg-green-100' : 'bg-red-100'
          }`}>
            {verificationResult === 'success' ? (
              <ShieldCheck className="w-8 h-8 text-green-600" />
            ) : (
              <ShieldAlert className="w-8 h-8 text-red-600" />
            )}
          </div>
          <div>
            <h3 className={`text-lg font-semibold ${
              verificationResult === 'success' ? 'text-green-900' : 'text-red-900'
            }`}>
              {verificationResult === 'success' ? 'Verification Successful' : 'Verification Failed'}
            </h3>
            <p className={`text-sm ${
              verificationResult === 'success' ? 'text-green-700' : 'text-red-700'
            }`}>
              {verificationResult === 'success'
                ? `Your connection with ${otherUserName} is now verified and secure.`
                : 'The verification process failed. Please try again or verify manually.'
              }
            </p>
          </div>
        </div>
      );
    }

    switch (currentStep) {
      case 'overview':
        return (
          <div className="space-y-6">
            <div className="text-center">
              <div className="w-16 h-16 bg-blue-100 rounded-full flex items-center justify-center mx-auto mb-4">
                <Shield className="w-8 h-8 text-blue-600" />
              </div>
              <h3 className="text-lg font-semibold text-gray-900 mb-2">
                Verify {otherUserName}
              </h3>
              <p className="text-sm text-gray-600">
                Verify your connection is secure by comparing security information with {otherUserName}.
              </p>
            </div>

            <div className="space-y-3">
              <Button
                onClick={() => setCurrentStep('qr')}
                className="w-full justify-start"
                variant="outline"
              >
                <QrCode className="w-5 h-5 mr-3" />
                <div className="text-left">
                  <div className="font-medium">Scan QR Code</div>
                  <div className="text-sm text-gray-500">Quick verification method</div>
                </div>
              </Button>

              <Button
                onClick={() => setCurrentStep('numbers')}
                className="w-full justify-start"
                variant="outline"
              >
                <Shield className="w-5 h-5 mr-3" />
                <div className="text-left">
                  <div className="font-medium">Compare Security Numbers</div>
                  <div className="text-sm text-gray-500">Manual verification method</div>
                </div>
              </Button>
            </div>

            <div className="p-3 bg-blue-50 rounded-lg">
              <p className="text-xs text-blue-800">
                <strong>Why verify?</strong> Verification ensures no one can intercept your messages by confirming you're talking to the right person.
              </p>
            </div>
          </div>
        );

      case 'qr':
        return (
          <div className="space-y-4">
            <div className="text-center">
              <h3 className="text-lg font-semibold text-gray-900 mb-2">
                QR Code Verification
              </h3>
              <p className="text-sm text-gray-600">
                Ask {otherUserName} to show their QR code and scan it with your camera.
              </p>
            </div>

            {currentStep === 'scan' ? (
              <QRCodeScanner
                onScan={handleQRScan}
                onError={(error) => console.error('QR Scan error:', error)}
                isActive={true}
              />
            ) : (
              <div className="space-y-4">
                <div className="bg-white border-2 border-gray-300 rounded-lg p-8 aspect-square flex items-center justify-center">
                  <div className="text-center">
                    <QrCode className="w-24 h-24 text-gray-400 mx-auto mb-4" />
                    <p className="text-sm text-gray-600">Your QR Code</p>
                    <p className="text-xs text-gray-500 mt-1">
                      Show this to {otherUserName}
                    </p>
                  </div>
                </div>
                
                <Button
                  onClick={() => setCurrentStep('scan')}
                  className="w-full"
                >
                  <Scan className="w-4 h-4 mr-2" />
                  Scan {otherUserName}'s QR Code
                </Button>
              </div>
            )}

            <Button
              variant="outline"
              onClick={() => setCurrentStep('overview')}
              className="w-full"
            >
              Back to Options
            </Button>
          </div>
        );

      case 'numbers':
        return (
          <div className="space-y-6">
            <SecurityNumberDisplay
              securityNumber={verificationData.securityNumber}
              otherUserName={otherUserName}
              onCopy={handleCopyNumbers}
              showNumbers={showNumbers}
              onToggleVisibility={() => setShowNumbers(!showNumbers)}
            />

            <div className="space-y-3">
              <p className="text-sm text-gray-600 text-center">
                Do the numbers match what {otherUserName} sees?
              </p>
              
              <div className="flex gap-3">
                <Button
                  variant="destructive"
                  onClick={() => handleManualVerification(false)}
                  disabled={isVerifying}
                  className="flex-1"
                >
                  <X className="w-4 h-4 mr-2" />
                  No, They Don't Match
                </Button>
                <Button
                  onClick={() => handleManualVerification(true)}
                  disabled={isVerifying}
                  className="flex-1"
                >
                  <CheckCircle className="w-4 h-4 mr-2" />
                  Yes, They Match
                </Button>
              </div>
            </div>

            <Button
              variant="outline"
              onClick={() => setCurrentStep('overview')}
              className="w-full"
            >
              Back to Options
            </Button>
          </div>
        );

      default:
        return null;
    }
  };

  // Reset state when dialog opens/closes
  useEffect(() => {
    if (isOpen) {
      setCurrentStep(hasKeyChanged ? 'overview' : 'overview');
      setVerificationResult(null);
      setIsVerifying(false);
      setShowNumbers(false);
    }
  }, [isOpen, hasKeyChanged]);

  return (
    <Dialog open={isOpen} onOpenChange={onClose}>
      <div className={`max-w-md mx-auto ${className}`}>
        <div className="p-6">
          {renderStepContent()}
        </div>
      </div>
    </Dialog>
  );
};

export default SecurityVerification;