import regex
from pathlib import Path
import shutil

# Main repository directories
repository_root = Path(__file__).parent.parent.resolve()
lean_source_dir = repository_root/'MIL'
sphinx_source_dir = repository_root/'sphinx_source'
user_repo_source_dir = repository_root/'user_repo_source'

# Generated directories
sphinx_dir = repository_root/'source'
sphinx_build_dir = repository_root/'build'
user_repo_dir = repository_root/'user_repo'
user_repo_lean_dir = user_repo_dir/'MIL'

# Generated files
lean_main_import_file = repository_root/'MIL.lean'
sphinx_index_file = sphinx_dir/'index.rst'
lean_user_main_import_file = user_repo_dir/'MIL.lean'

def clean_generated_directories():
    """
    Deletes automatically generated directories.
    """
    if sphinx_dir.exists():
        shutil.rmtree(sphinx_dir)
    if sphinx_build_dir.exists():
        shutil.rmtree(sphinx_build_dir)
    if user_repo_dir.exists():
        shutil.rmtree(user_repo_dir)

def ensure_generated_directories_exist():
    """
    Makes sure the Sphinx source and user repo directories exist.
    """
    if not sphinx_dir.exists():
        sphinx_dir.mkdir()
    if not user_repo_lean_dir.exists():
        user_repo_lean_dir.mkdir(parents=True)

def make_lean_main_import_file():
    """
    Generates a Lean file with all the imports.
    """
    with lean_main_import_file.open('w', encoding='utf8') as import_file:
        chapter_dirs = sorted(
            [dir for dir in lean_source_dir.glob("C*") if dir.is_dir()],
            key=lambda d: d.name)
        for chapter_dir in chapter_dirs:
            section_files= sorted([file for file in chapter_dir.glob("S*.lean")], key=lambda f: f.name)
            for section_file in section_files:
                section_name = section_file.name[:-5]
                import_file.write(f"import MIL.{chapter_dir.name}.{section_name}\n")

def make_lean_user_main_import_file():
    """
    Generates a Lean file with all imports for all the exercise files in the user repository.
    """
    if not user_repo_lean_dir.exists():
        user_repo_lean_dir.mkdir(parents=True)
    with lean_user_main_import_file.open('w', encoding='utf8') as import_file:
        chapter_dirs = sorted(
            [dir for dir in lean_source_dir.glob("C*") if dir.is_dir()],
            key=lambda d: d.name)
        for chapter_dir in chapter_dirs:
            section_files= sorted([file for file in chapter_dir.glob("S*.lean")], key=lambda f: f.name)
            for section_file in section_files:
                section_name = section_file.name[:-5]
                import_file.write(f"import MIL.{chapter_dir.name}.{section_name}\n")

index_file_start = """
Mathematics in Lean
===================

.. toctree::
   :numbered:
   :maxdepth: 2

"""

index_file_end = """
.. toctree::
   :hidden:

   genindex
"""

def make_sphinx_index_file():
    """
    Generates the index file in the Sphinx source directory.
    """
    ensure_generated_directories_exist()
    with sphinx_index_file.open('w', encoding='utf8') as index_file:
        index_file.write(index_file_start)
        chapter_dirs = sorted(
            [dir for dir in lean_source_dir.glob("C*") if dir.is_dir()],
            key=lambda d: d.name)
        for chapter_dir in chapter_dirs:
            index_file.write("   " + chapter_dir.name + "\n")
        index_file.write(index_file_end)

def make_sphinx_chapter_files():
    """
    Generates the chapter files in the Sphinx source directory.
    """
    ensure_generated_directories_exist()
    chapter_dirs = sorted(
        [dir for dir in lean_source_dir.glob("C*") if dir.is_dir()],
        key=lambda d: d.name)
    for chapter_dir in chapter_dirs:
        chapter_name = chapter_dir.name
        chapter_file = chapter_dir/(chapter_name + ".rst")
        shutil.copy2(chapter_file, sphinx_dir)
        dest_file = sphinx_dir/(chapter_name + ".rst")
        with dest_file.open('a', encoding='utf8') as dest:
            dest.write("\n")
            section_files= sorted(
                [file for file in chapter_dir.glob("S*.lean")],
                key=lambda f: f.name)
            for section_file in section_files:
                section_name = section_file.name[:-5]
                dest.write(f".. include:: {chapter_name}/{section_name}.inc\n")

# Regular expressions for parsing Lean source directives
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

def process_section(chapter_name, section_name):
    """
    Creates the user repository examples file, the user repository solutions file, and the
    Sphinx section file associated with a Lean section source file.
    """
    lean_source_file = lean_source_dir/chapter_name/(section_name + '.lean')
    if not lean_source_file.exists():
        raise Exception (f'File {lean_source_file.name()} not found')

    ensure_generated_directories_exist()
    print('processing {0}/{1}'.format(chapter_name, section_name))

    sphinx_chapter_dir = sphinx_dir/chapter_name
    if not sphinx_chapter_dir.exists():
        sphinx_chapter_dir.mkdir()
    sphinx_section_file = sphinx_chapter_dir/(section_name + '.inc')

    user_repo_chapter_dir = user_repo_lean_dir/chapter_name
    user_repo_chapter_solutions_dir = user_repo_chapter_dir/'solutions'
    if not user_repo_chapter_solutions_dir.exists():
        user_repo_chapter_solutions_dir.mkdir(parents=True)

    user_repo_examples_file = user_repo_chapter_dir/(section_name + '.lean')
    user_repo_solutions_file = user_repo_chapter_solutions_dir/('Solutions_' + section_name + '.lean')

    with lean_source_file.open(encoding='utf8') as source_file, \
            sphinx_section_file.open('w', encoding='utf8') as rst_file, \
            user_repo_examples_file.open('w', encoding='utf8') as examples_file, \
            user_repo_solutions_file.open('w', encoding='utf8') as solutions_file:
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
                rst_file.write(".. literalinclude:: /../MIL/{}/{}.lean\n".format(chapter_name, section_name))
                rst_file.write("   :start-after: -- TAG: {}\n".format(tag))
                rst_file.write("   :end-before: -- TAG: end\n")
            # Content lines.
            else:
                line = line.replace(dummy_chars, '')
                if mode == 'main':
                    examples_file.write(line)
                elif mode == 'solutions':
                    solutions_file.write(line)
                elif mode == 'both':
                    examples_file.write(line)
                    solutions_file.write(line)
                elif mode == 'omit':
                    pass
                elif mode == 'text':
                    rst_file.write(line)
                else:
                    raise RuntimeError("unexpected mode")
                if quoting and mode != 'solutions':
                    rst_file.write('  ' + line)

def process_sections():
    """
    Processes all the sections.
    """
    chapter_dirs = sorted(
        [dir for dir in lean_source_dir.glob("C*") if dir.is_dir()],
        key=lambda d: d.name)
    for chapter_dir in chapter_dirs:
        section_files= sorted(
            [file for file in chapter_dir.glob("S*.lean")],
            key=lambda f: f.name)
        for section_file in section_files:
            section_name = section_file.name[:-5]
            process_section(chapter_dir.name, section_name)

def make_everything():
    """
    Generates all the files that should be automatically generated, other than the ones
    that are generated by Sphinx.
    """

    # remove generated directories (other than build)
    if sphinx_dir.exists():
        shutil.rmtree(sphinx_dir)
    if user_repo_dir.exists():
        shutil.rmtree(user_repo_dir)

    # make the main import file
    make_lean_main_import_file()

    # copy initial files to the user repo
    shutil.copytree(user_repo_source_dir, user_repo_dir)

    # create the main subdirectory in the user repo
    user_repo_lean_dir.mkdir()

    # copy Lean configuration files to the user repo
    shutil.copy2(repository_root/'lake-manifest.json', user_repo_dir)
    shutil.copy2(repository_root/'lakefile.lean', user_repo_dir)
    shutil.copy2(repository_root/'lean-toolchain', user_repo_dir)
    shutil.copy2(repository_root/'MIL'/'Common.lean', user_repo_dir/'MIL')

    # make the main import file in the user repo
    make_lean_user_main_import_file()

    # copy initial files to the Sphinx folder
    shutil.copytree(sphinx_source_dir, sphinx_dir)

    # start generating Sphinx source files
    make_sphinx_index_file()
    make_sphinx_chapter_files()

    # generate the examples files, solutions files, and Sphinx files for each section
    process_sections()

def make_examples_test():
    """
    Assuming the `user_repo` has been built, this copies the examples files and solutions files into
    a test folder, and replaces the main build repository import file with a file that imports
    all the examples files.
    """
    test_dir = lean_source_dir/"Test"
    if test_dir.exists():
        shutil.rmtree(test_dir)
    shutil.copytree(user_repo_lean_dir, test_dir)

    # TODO: this is copy-pasted-modified from make_lean_user_main_import_file()
    with lean_main_import_file.open('w', encoding='utf8') as import_file:
        chapter_dirs = sorted(
            [dir for dir in lean_source_dir.glob("C*") if dir.is_dir()],
            key=lambda d: d.name)
        for chapter_dir in chapter_dirs:
            section_files= sorted([file for file in chapter_dir.glob("S*.lean")], key=lambda f: f.name)
            for section_file in section_files:
                section_name = section_file.name[:-5]
                import_file.write(f"import MIL.Test.{chapter_dir.name}.{section_name}\n")

def make_solutions_test():
    """
    Assuming the `user_repo` has been built, this copies the examples files and solutions files into
    a test folder, and replaces the main build repository import file with a file that imports
    all the solutions files.
    """
    test_dir = lean_source_dir/"Test"
    if test_dir.exists():
        shutil.rmtree(test_dir)
    shutil.copytree(user_repo_lean_dir, test_dir)

    # TODO: this is copy-pasted-modified from the procedure above()
    with lean_main_import_file.open('w', encoding='utf8') as import_file:
        chapter_dirs = sorted(
            [dir for dir in lean_source_dir.glob("C*") if dir.is_dir()],
            key=lambda d: d.name)
        for chapter_dir in chapter_dirs:
            section_files= sorted([file for file in chapter_dir.glob("S*.lean")], key=lambda f: f.name)
            for section_file in section_files:
                section_name = section_file.name[:-5]
                import_file.write(f"import MIL.Test.{chapter_dir.name}.solutions.Solutions_{section_name}\n")

def clean_test():
    """
    Removes the test folder and restores the main import file.
    """
    test_dir = lean_source_dir/"Test"
    if test_dir.exists():
        shutil.rmtree(test_dir)
    make_lean_main_import_file()
