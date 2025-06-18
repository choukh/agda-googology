#!/usr/bin/env python3
"""
Text transformation script that performs the following steps:
1. Replace all ## with #
2. Replace all $$ with ††
3. Replace all $ with $$
4. Replace all †† with $$
"""

import sys
import argparse

def transform_text(text):
    """Apply the transformation steps in order."""
    # Step 1: Replace all ## with #
    text = text.replace('##', '#')
    
    # Step 2: Replace all $$ with ††
    text = text.replace('$$', '††')
    
    # Step 3: Replace all $ with $$
    text = text.replace('$', '$$')
    
    # Step 4: Replace all †† with $$
    text = text.replace('††', '$$')
    
    return text

def main():
    parser = argparse.ArgumentParser(description='Transform text file with specific replacements')
    parser.add_argument('input_file', help='Input file path')
    parser.add_argument('output_file', help='Output file path')
    
    args = parser.parse_args()
    
    try:
        # Read input file
        with open(args.input_file, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Transform the content
        transformed_content = transform_text(content)
        
        # Write output file
        with open(args.output_file, 'w', encoding='utf-8') as f:
            f.write(transformed_content)
        
        print(f"Successfully transformed {args.input_file} -> {args.output_file}")
        
    except FileNotFoundError:
        print(f"Error: Input file '{args.input_file}' not found", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == '__main__':
    main()