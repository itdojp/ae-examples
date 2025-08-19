import React from 'react';

interface QRCodeProps {
  data: string;
  size?: number;
}

const QRCode: React.FC<QRCodeProps> = ({ data, size = 200 }) => {
  return (
    <div className="qr-code" style={{ width: size, height: size }}>
      <div className="qr-placeholder">
        <svg
          width={size}
          height={size}
          viewBox="0 0 200 200"
          fill="none"
          xmlns="http://www.w3.org/2000/svg"
        >
          <rect width="200" height="200" fill="white"/>
          <rect x="10" y="10" width="60" height="60" fill="black"/>
          <rect x="20" y="20" width="40" height="40" fill="white"/>
          <rect x="30" y="30" width="20" height="20" fill="black"/>
          
          <rect x="130" y="10" width="60" height="60" fill="black"/>
          <rect x="140" y="20" width="40" height="40" fill="white"/>
          <rect x="150" y="30" width="20" height="20" fill="black"/>
          
          <rect x="10" y="130" width="60" height="60" fill="black"/>
          <rect x="20" y="140" width="40" height="40" fill="white"/>
          <rect x="30" y="150" width="20" height="20" fill="black"/>
          
          {[...Array(5)].map((_, i) => (
            <g key={i}>
              <rect x={80 + i * 10} y="10" width="8" height="8" fill={i % 2 === 0 ? "black" : "white"}/>
              <rect x={80 + i * 10} y="20" width="8" height="8" fill={i % 2 === 1 ? "black" : "white"}/>
              <rect x={80 + i * 10} y="30" width="8" height="8" fill={i % 2 === 0 ? "black" : "white"}/>
            </g>
          ))}
          
          <text
            x="100"
            y="110"
            textAnchor="middle"
            fontSize="10"
            fill="#666"
            fontFamily="monospace"
          >
            {data.substring(0, 8)}...
          </text>
        </svg>
      </div>
      
      <style jsx>{`
        .qr-code {
          display: inline-block;
          padding: 16px;
          background: white;
          border: 1px solid #e0e0e0;
          border-radius: 8px;
        }
        
        .qr-placeholder {
          width: 100%;
          height: 100%;
          display: flex;
          align-items: center;
          justify-content: center;
        }
      `}</style>
    </div>
  );
};

export default QRCode;