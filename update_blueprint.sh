#!/bin/bash

# Blueprint Update Script for TM_Tape_to_Number
# This script builds the Lean project, updates the blueprint, and opens it

set -e  # Exit on error

echo "==================================="
echo "TM_Tape_to_Number Blueprint Updater"
echo "==================================="
echo ""

# Get the directory where this script is located
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$SCRIPT_DIR"

echo "📦 Building Lean project..."
echo "-----------------------------------"
lake build 2>&1 | tee build_output.txt
if [ ${PIPESTATUS[0]} -eq 0 ]; then
    echo "✅ Lean build successful!"
else
    echo "❌ Lean build failed. Check build_output.txt for details."
    exit 1
fi

echo ""
echo "🔨 Building blueprint..."
echo "-----------------------------------"
# Build the blueprint web version
leanblueprint web
if [ $? -eq 0 ]; then
    echo "✅ Blueprint build successful!"
else
    echo "❌ Blueprint build failed."
    exit 1
fi

# Check if Lean docs are available and copy them
if [ -d ".lake/build/doc" ]; then
    echo ""
    echo "📚 Copying Lean documentation..."
    mkdir -p blueprint/web/docs
    cp -r .lake/build/doc/* blueprint/web/docs/
    echo "✅ Lean docs copied - links will work locally!"
fi

echo ""
echo "🌐 Starting web server and opening blueprint..."
echo "-----------------------------------"

# Kill any existing Python servers on port 8000
lsof -ti:8000 | xargs kill -9 2>/dev/null || true

# Start the server in the background
cd blueprint/web
python3 -m http.server 8000 > /dev/null 2>&1 &
SERVER_PID=$!
cd ../..

# Give the server a moment to start
sleep 1

# Open the dependency graph in browser
if [[ "$OSTYPE" == "darwin"* ]]; then
    # macOS
    open "http://localhost:8000/dep_graph_document.html"
elif [[ "$OSTYPE" == "linux-gnu"* ]]; then
    # Linux
    xdg-open "http://localhost:8000/dep_graph_document.html" 2>/dev/null || sensible-browser "http://localhost:8000/dep_graph_document.html"
else
    echo "⚠️  Please open http://localhost:8000/dep_graph_document.html manually"
fi

echo ""
echo "✨ Blueprint ready!"
echo "-----------------------------------"
echo "📊 Dependency graph: http://localhost:8000/dep_graph_document.html"
echo "📄 Main content: http://localhost:8000/index.html"
echo ""
echo "🔴 Server running on PID $SERVER_PID"
echo "   To stop the server: kill $SERVER_PID"
echo "   Or press Ctrl+C to stop this script"
echo ""
echo "ℹ️  Note: Lean documentation links will work once deployed to GitHub Pages"

# Keep the script running so the server stays up
trap "kill $SERVER_PID 2>/dev/null; echo ''; echo '🛑 Server stopped'" EXIT
echo "Press Ctrl+C to stop the server..."
wait $SERVER_PID