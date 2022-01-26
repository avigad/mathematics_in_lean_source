#!/usr/bin/env python3

import sys
import regex
from pathlib import Path

chapter_name = sys.argv[1]
section_name = sys.argv[2]

# Paths to input and output files.
root = Path(__file__).parent
source_path = root/chapter_name/('source_' + section_name + '.lean')
rst_chapter_path = root.resolve().parent/'source'/chapter_name
if not rst_chapter_path.exists():
    rst_chapter_path.mkdir()
rst_path = rst_chapter_path/(section_name + '.inc')
lean_chapter_path = root.resolve().parent/'src'/chapter_name
if not lean_chapter_path.exists():
    lean_chapter_path.mkdir()
lean_solutions_path = lean_chapter_path/'solutions'
if not lean_solutions_path.exists():
    lean_solutions_path.mkdir()
lean_file_path = lean_chapter_path/(section_name + '.lean')
solutions_path = lean_solutions_path/('solutions_' + section_name + '.lean')

# Regular expressions.
main_mode = regex.compile(r'-- EXAMPLES:.*|/- EXAMPLES:.*|EXAMPLES: -/.*')
both_mode = regex.compile(r'-- BOTH:.*|/- BOTH:.*|BOTH: -/.*')
solutions_mode = regex.compile(r'-- SOLUTIONS:.*|/- SOLUTIONS:.*|SOLUTIONS: -/.*')
omit_mode = regex.compile(r'-- OMIT:.*|/- OMIT:.*|OMIT: -/.*')
tag_line = regex.compile(r'-- TAG:.*')
text_start = regex.compile(r'/- TEXT:.*')
text_end = regex.compile(r'TEXT\. -/.*')
quote_start = regex.compile(r'-- QUOTE:.*')
quote_end = regex.compile(r'-- QUOTE\..*')
literalinclude = regex.compile(r'-- LITERALINCLUDE: (.*)')

# Used to avoid name collisions.
dummy_chars = 'αα'

if __name__ == '__main__':
    with source_path.open(encoding='utf8') as source_file, \
            rst_path.open('w', encoding='utf8') as rst_file, \
            lean_file_path.open('w', encoding='utf8') as lean_file, \
            solutions_path.open('w', encoding='utf8') as solutions:
        mode = 'both'
        quoting = False
        line_num = 0
        for line in source_file:
            line_num += 1
            # Command lines.
            if main_mode.match(line):
                mode = 'main'
            elif both_mode.match(line):
                mode = 'both'
            elif solutions_mode.match(line):
                mode = 'solutions'
            elif omit_mode.match(line):
                mode = 'omit'
            elif tag_line.match(line):
                # For quoting from the source; simply remove from output.
                pass
            elif text_start.match(line):
                mode = 'text'
            elif text_end.match(line):
                mode = 'main'
            elif quote_start.match(line):
                if quoting:
                    raise RuntimeError(
                        "{0}: '-- QUOTE:' while already quoting".format(line_num))
                if mode == 'text':
                    raise RuntimeError("{0}: '-- QUOTE:' while in text mode".format(line_num))
                rst_file.write('\n.. code-block:: lean\n\n')
                quoting = True
            elif quote_end.match(line):
                if not quoting:
                    raise RuntimeError("{0}: '-- QUOTE.' while not quoting".format(line_num))
                rst_file.write('\n')
                quoting = False
            elif match_literalinclude := literalinclude.match(line):
                tag = match_literalinclude.group(1)
                rst_file.write(".. literalinclude:: /../lean_source/{}/source_{}.lean\n".format(chapter_name, section_name))
                rst_file.write("   :start-after: -- TAG: {}\n".format(tag))
                rst_file.write("   :end-before: -- TAG: end\n")
            # Content lines.
            else:
                line = line.replace(dummy_chars, '')
                if mode == 'main':
                    lean_file.write(line)
                elif mode == 'solutions':
                    solutions.write(line)
                elif mode == 'both':
                    lean_file.write(line)
                    solutions.write(line)
                elif mode == 'omit':
                    pass
                elif mode == 'text':
                    rst_file.write(line)
                else:
                    raise RuntimeError("unexpected mode")
                if quoting and mode != 'solutions':
                    rst_file.write('  ' + line)