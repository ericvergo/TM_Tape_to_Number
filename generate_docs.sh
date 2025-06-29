#!/bin/bash

# Generate Lean Documentation Script

set -e

echo "📚 Generating Lean Documentation..."
echo "==================================="
echo ""

# Build the documentation
echo "Building documentation (this may take a while)..."
lake build TMTapeToNumber:docs

# The docs should be in .lake/build/doc
if [ -d ".lake/build/doc" ]; then
    echo ""
    echo "✅ Documentation built successfully!"
    echo ""
    echo "Copying to blueprint/web/docs for local viewing..."
    
    # Create docs directory in blueprint
    mkdir -p blueprint/web/docs
    
    # Copy the documentation
    cp -r .lake/build/doc/* blueprint/web/docs/
    
    echo ""
    echo "📂 Documentation available at:"
    echo "  - Local: blueprint/web/docs/index.html"
    echo "  - When served: http://localhost:8000/docs/"
    echo ""
    echo "The blueprint Lean links will now work when viewing locally!"
else
    echo "❌ Documentation build failed or output not found"
    exit 1
fi