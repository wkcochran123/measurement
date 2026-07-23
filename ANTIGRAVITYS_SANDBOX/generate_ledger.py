#!/usr/bin/env python3
import os
import re

def escape_latex(text):
    if not text:
        return ""
    # Replace backslash first
    text = text.replace('\\', '\\textbackslash{}')
    # Replace other special characters
    specials = {
        '&': '\\&',
        '%': '\\%',
        '$': '\\$',
        '#': '\\#',
        '_': '\\_',
        '{': '\\{',
        '}': '\\}',
        '~': '\\textasciitilde{}',
        '^': '\\textasciicircum{}',
    }
    for char, esc in specials.items():
        text = text.replace(char, esc)
    # Replace common Unicode math symbols that pdflatex cannot render in text
    unicode_math = {
        '≈': '\\ensuremath{\\approx}',
        'α': '\\ensuremath{\\alpha}',
        '·': '\\ensuremath{\\cdot}',
        '≤': '\\ensuremath{\\le}',
        '≥': '\\ensuremath{\\ge}',
        '≠': '\\ensuremath{\\neq}',
        '±': '\\ensuremath{\\pm}',
        '→': '\\ensuremath{\\to}',
        '⊆': '\\ensuremath{\\subseteq}',
        'ε': '\\ensuremath{\\varepsilon}',
        'μ': '\\ensuremath{\\mu}',
        '∧': '\\ensuremath{\\land}',
        '∨': '\\ensuremath{\\lor}',
        '¬': '\\ensuremath{\\neg}',
        '⟨': '\\ensuremath{\\langle}',
        '⟩': '\\ensuremath{\\rangle}',
        '∀': '\\ensuremath{\\forall}',
        '∃': '\\ensuremath{\\exists}',
        '⇒': '\\ensuremath{\\Rightarrow}',
        '∈': '\\ensuremath{\\in}',
        '←': '\\ensuremath{\\leftarrow}',
        '×': '\\ensuremath{\\times}',
    }
    for char, esc in unicode_math.items():
        text = text.replace(char, esc)
    return text

def parse_structure_or_class(lines, start_idx):
    fields = []
    i = start_idx + 1
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        
        # Stop scanning if we hit a new declaration or top-level keyword
        if stripped and not line.startswith(' ') and not line.startswith('\t') and not stripped.startswith('--') and not stripped.startswith('/-'):
            break
        if re.match(r'^\s*(def|theorem|inductive|class|structure|instance|open|namespace|end)\b', stripped):
            break
            
        # Parse fields: must have ':' and not ':='
        if ':' in stripped and ':=' not in stripped and not stripped.startswith('--') and not stripped.startswith('/-'):
            # Handle comments at end of line
            field_code = stripped.split('--')[0].strip()
            if ':' in field_code:
                parts = field_code.split(':', 1)
                field_name = parts[0].strip().strip('(){}[]')
                field_type = parts[1].strip()
                if field_name and field_type:
                    fields.append((field_name, field_type))
        i += 1
    return fields

def parse_inductive(lines, start_idx):
    constructors = []
    i = start_idx + 1
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        
        # Stop scanning if we hit a new declaration
        if stripped and not line.startswith(' ') and not line.startswith('\t') and not stripped.startswith('|') and not stripped.startswith('--') and not stripped.startswith('/-'):
            break
        if re.match(r'^\s*(def|theorem|inductive|class|structure|instance|open|namespace|end)\b', stripped):
            break
            
        if stripped.startswith('|'):
            # Parse constructor: e.g. | zero : Fact -> Natural
            const_code = stripped[1:].strip().split('--')[0].strip()
            if ':' in const_code:
                parts = const_code.split(':', 1)
                const_name = parts[0].strip()
                const_type = parts[1].strip()
                constructors.append((const_name, const_type))
            else:
                constructors.append((const_code, ""))
        i += 1
    return constructors

def parse_file(filepath):
    filename = os.path.basename(filepath)
    print(f"Parsing {filename}...")
    
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
        
    decls = []
    
    # Track comments
    comment_accumulator = []
    in_block_comment = False
    block_comment_lines = []
    
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        
        # Block comments
        if '/-' in line:
            in_block_comment = True
            block_comment_lines = []
            start_idx = line.find('/-') + 2
            block_comment_lines.append(line[start_idx:])
            if '-/' in line:
                in_block_comment = False
                block_comment_lines[-1] = block_comment_lines[-1].split('-/')[0]
                comment_accumulator = [" ".join(block_comment_lines).strip()]
            i += 1
            continue
            
        if in_block_comment:
            if '-/' in line:
                in_block_comment = False
                end_idx = line.find('-/')
                block_comment_lines.append(line[:end_idx])
                comment_accumulator = ["\n".join(block_comment_lines).strip()]
            else:
                block_comment_lines.append(line)
            i += 1
            continue
            
        # Line comments
        if stripped.startswith('--'):
            comment_accumulator.append(stripped[2:].strip())
            i += 1
            continue
            
        # Detect declarations
        match = re.match(r'^\s*(class|structure|inductive|instance)\b', line)
        if match:
            decl_type = match.group(1)
            line_num = i + 1
            decl_header = line.strip()
            
            # Look for end of line comment
            eol_comment = ""
            if '--' in line:
                parts = line.split('--', 1)
                decl_header = parts[0].strip()
                eol_comment = parts[1].strip()
                
            desc = ""
            if comment_accumulator:
                desc = "\n".join(comment_accumulator).strip()
                comment_accumulator = []
            elif eol_comment:
                desc = eol_comment
                
            # Extract name
            decl_words = decl_header.split()
            decl_name = ""
            if len(decl_words) > 1:
                decl_name = decl_words[1]
                if decl_name == ":" or decl_name.startswith(":"):
                    decl_name = " ".join(decl_words[1:])
            else:
                decl_name = decl_type
                
            # Perform structural parsing depending on the type
            fields = []
            constructors = []
            
            if decl_type in ['structure', 'class']:
                fields = parse_structure_or_class(lines, i)
            elif decl_type == 'inductive':
                constructors = parse_inductive(lines, i)
                
            decls.append({
                'type': decl_type,
                'name': decl_name,
                'header': decl_header,
                'line': line_num,
                'desc': desc,
                'fields': fields,
                'constructors': constructors
            })
        elif stripped == "":
            comment_accumulator = []
            
        i += 1
        
    return decls

def main():
    device_dir = "/Users/williamcochran/Desktop/measurement/device/Measurement"
    
    # 1. Collect all Episode files and sort them numerically
    episode_files = []
    for f in os.listdir(device_dir):
        if f.startswith("Episode") and f.endswith(".lean"):
            num_match = re.search(r'Episode(\d+)\.lean', f)
            if num_match:
                num = int(num_match.group(1))
                episode_files.append((num, os.path.join(device_dir, f)))
                
    episode_files.sort(key=lambda x: x[0])
    sorted_filepaths = [x[1] for x in episode_files]
    
    # 2. Add surface files
    surface_files = [
        "TwoDescriptions.lean",
        "AlphaBoundCountToThree.lean",
        "AlphaBoundMediant.lean",
        "SelfApplication.lean",
        "CalibrationTwoPaths.lean",
        "FinitenessFence.lean"
    ]
    for sf in surface_files:
        path = os.path.join(device_dir, sf)
        if os.path.exists(path):
            sorted_filepaths.append(path)
            
    # 3. Parse all files and generate LaTeX content
    latex_output = []
    latex_output.append("\\chapter{The Complete Ledger of Logical Declarations}\n")
    latex_output.append("This chapter lists every single \\lean{inductive}, \\lean{class}, \\lean{structure}, and \\lean{instance} declaration in the codebase from start to finish, providing a conceptual analysis of their types, fields, constructors, and logical relations. No code blocks are reproduced.\n\n")
    
    for filepath in sorted_filepaths:
        decls = parse_file(filepath)
        if not decls:
            continue
            
        filename = os.path.basename(filepath)
        safe_filename = filename.replace('_', '\\_')
        latex_output.append(f"\\section{{File: {safe_filename}}}\n")
        
        for d in decls:
            safe_name = d['name'].replace('_', '\\_')
            latex_output.append("\\subsection{" + d['type'].capitalize() + " " + safe_name + " (Line " + str(d['line']) + ")}\n")
            
            # Print the conceptual breakdown instead of the raw code block
            latex_output.append("This declaration represents a logical ")
            if d['type'] == 'structure':
                latex_output.append("record structure named \\lean{" + safe_name + "}. It constructs records using the constructor \\lean{" + safe_name + ".mk} with the following fields:\n")
                if d['fields']:
                    latex_output.append("\\begin{description}\n")
                    for fname, ftype in d['fields']:
                        safe_fname = fname.replace('_', '\\_')
                        escaped_ftype = escape_latex(ftype)
                        latex_output.append("  \\item[\\lean{" + safe_fname + "}] \\ensuremath{\\to} type signature: \\lean{" + escaped_ftype + "}\n")
                    latex_output.append("\\end{description}\n")
                else:
                    latex_output.append("No record fields are explicitly declared (flat or marker structure).\n\n")
            elif d['type'] == 'class':
                latex_output.append("typeclass constraint named \\lean{" + safe_name + "}. It defines type-level predicates and methods that must be satisfied during compilation. The methods are:\n")
                if d['fields']:
                    latex_output.append("\\begin{description}\n")
                    for fname, ftype in d['fields']:
                        safe_fname = fname.replace('_', '\\_')
                        escaped_ftype = escape_latex(ftype)
                        latex_output.append("  \\item[\\lean{" + safe_fname + "}] \\ensuremath{\\to} method signature: \\lean{" + escaped_ftype + "}\n")
                    latex_output.append("\\end{description}\n")
                else:
                    latex_output.append("No class methods are explicitly declared (marker or type predicate).\n\n")
            elif d['type'] == 'inductive':
                latex_output.append("constructive sum type named \\lean{" + safe_name + "}. It represents a disjoint union populated by the following constructors:\n")
                if d['constructors']:
                    latex_output.append("\\begin{description}\n")
                    for cname, ctype in d['constructors']:
                        safe_cname = cname.replace('_', '\\_')
                        escaped_ctype = escape_latex(ctype) if ctype else "No parameter constructor"
                        latex_output.append("  \\item[\\lean{" + safe_cname + "}] \\ensuremath{\\to} constructor signature: \\lean{" + escaped_ctype + "}\n")
                    latex_output.append("\\end{description}\n")
                else:
                    latex_output.append("No constructors are explicitly declared.\n\n")
            elif d['type'] == 'instance':
                # Parse typeclass and target from header
                # e.g., instance : LE Sum := ...
                latex_output.append("typeclass instance registration. It instantiates the typeclass relation described by \\lean{" + escape_latex(d['header']) + "}.\n\n")
            
            if d['desc']:
                escaped_desc = escape_latex(d['desc'])
                latex_output.append("\\textbf{Implementation Commentary:}\\\\\n" + escaped_desc + "\n\n")
            else:
                latex_output.append("\\textbf{Implementation Commentary:}\\\\\nNo local comments provided.\n\n")
                
    # 4. Read book.tex, locate insert point, and overwrite
    book_tex_path = "/Users/williamcochran/Desktop/measurement/ANTIGRAVITYS_SANDBOX/book.tex"
    with open(book_tex_path, 'r', encoding='utf-8') as f:
        book_content = f.read()
        
    start_marker = "% LEDGER_START"
    end_marker = "% LEDGER_END"
    
    if start_marker in book_content and end_marker in book_content:
        parts_start = book_content.split(start_marker, 1)
        parts_end = parts_start[1].split(end_marker, 1)
        new_book_content = parts_start[0] + start_marker + "\n" + "".join(latex_output) + "\n" + end_marker + parts_end[1]
    else:
        split_marker = "\\end{document}"
        if split_marker in book_content:
            parts = book_content.split(split_marker, 1)
            new_book_content = parts[0] + "\n" + start_marker + "\n" + "".join(latex_output) + "\n" + end_marker + "\n" + split_marker + parts[1]
        else:
            print("Error: Could not find \\end{document} in book.tex")
            return
            
    with open(book_tex_path, 'w', encoding='utf-8') as f:
        f.write(new_book_content)
    print("Successfully updated book.tex with the complete ledger!")

if __name__ == "__main__":
    main()
