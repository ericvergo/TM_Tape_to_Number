#!/bin/bash

# Serve Blueprint with Python HTTP Server
# This avoids CORS issues with WebAssembly

echo "🌐 Starting blueprint server..."
echo "-----------------------------------"
echo "Blueprint will be available at: http://localhost:8000"
echo "Press Ctrl+C to stop the server"
echo ""

cd blueprint/web
python3 -m http.server 8000