import React from 'react';
import { User } from '@e2e-chat/shared';

interface UserListProps {
  users: User[];
  selectedUser: User | null;
  onSelectUser: (user: User) => void;
}

export default function UserList({ users, selectedUser, onSelectUser }: UserListProps) {
  return (
    <div className="flex-1 overflow-y-auto">
      <div className="p-4">
        <h3 className="text-sm font-semibold text-gray-500 uppercase tracking-wider mb-3">
          Contacts
        </h3>
        <div className="space-y-1">
          {users.map((user) => (
            <button
              key={user.id}
              onClick={() => onSelectUser(user)}
              className={`w-full text-left px-4 py-3 rounded-lg transition duration-200 ${
                selectedUser?.id === user.id
                  ? 'bg-blue-50 border-l-4 border-blue-600'
                  : 'hover:bg-gray-50'
              }`}
            >
              <div className="flex items-center">
                <div className="w-10 h-10 bg-gradient-to-br from-blue-400 to-blue-600 rounded-full flex items-center justify-center text-white font-semibold">
                  {user.displayName.charAt(0).toUpperCase()}
                </div>
                <div className="ml-3">
                  <p className="font-medium text-gray-800">{user.displayName}</p>
                  <p className="text-sm text-gray-500">{user.email}</p>
                </div>
              </div>
            </button>
          ))}
        </div>
      </div>
    </div>
  );
}