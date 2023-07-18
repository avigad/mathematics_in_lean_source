#!/usr/bin/env python3
import sys
from mkdoc import process_section

if __name__ == '__main__':
    chapter_name = sys.argv[1]
    section_name = sys.argv[2]
    process_section(chapter_name, section_name)
