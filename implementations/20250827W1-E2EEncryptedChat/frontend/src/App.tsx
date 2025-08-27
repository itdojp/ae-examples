import React from 'react';
import { BrowserRouter as Router, Routes, Route, Navigate } from 'react-router-dom';
import { Toaster } from 'react-hot-toast';
import { useAuthStore } from './stores/authStore';
import Login from './components/Login';
import Register from './components/Register';
import Chat from './components/Chat';

function App() {
  const { token } = useAuthStore();

  return (
    <Router>
      <div className="min-h-screen bg-gray-100">
        <Toaster position="top-right" />
        <Routes>
          <Route path="/login" element={!token ? <Login /> : <Navigate to="/chat" />} />
          <Route path="/register" element={!token ? <Register /> : <Navigate to="/chat" />} />
          <Route path="/chat" element={token ? <Chat /> : <Navigate to="/login" />} />
          <Route path="/" element={<Navigate to={token ? "/chat" : "/login"} />} />
        </Routes>
      </div>
    </Router>
  );
}

export default App;