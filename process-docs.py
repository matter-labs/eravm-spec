from typing import List
import re
import subprocess
import sys
import pypandoc
import os

KATEX_SUPPORT_HEADER = """
  <script defer=""
  src="https://cdn.jsdelivr.net/npm/katex@0.15.1/dist/katex.min.js"></script>
  <script>document.addEventListener("DOMContentLoaded", function () {
 var mathElements = document.getElementsByClassName("math");
 var macros = [];
 for (var i = 0; i < mathElements.length; i++) {
  var texText = mathElements[i].firstChild;
  if (mathElements[i].tagName == "SPAN") {
   katex.render(texText.data, mathElements[i], {
    displayMode: mathElements[i].classList.contains('display'),
    throwOnError: false,
    macros: macros,
    fleqn: false
   });
}}});
  </script>
  <link rel="stylesheet"
  href="https://cdn.jsdelivr.net/npm/katex@0.15.1/dist/katex.min.css" />
"""

def process_region(text:str)->str:
    return pypandoc.convert_text(text, to='html', format='markdown', extra_args=['--katex'])

def process_file(file_name_in:str, file_name_out:str, processor) -> None:
    with open(file_name_in, 'r') as file:
        data = file.read()

    modified_data = re.sub(
        r'%DOCSTART%(.*?)%DOCEND%',
        lambda match: processor(match.group(1)),
        data,
        flags=re.DOTALL
    )
    # modified_data = re.sub(
    #     r'<pre>(.*?)</pre>',
    #     lambda match: processor(match.group(1)),
    #     data,
    #     flags=re.DOTALL
    # )
    modified_data = re.sub(
        r'</head>',
        KATEX_SUPPORT_HEADER + "</head>",
        modified_data)

    with open(file_name_out, 'w') as file:
        file.write(modified_data)

def process_dir(directory_path:str):
    for root, dirs, files in os.walk(directory_path):
        for filename in files:
            if filename.lower().endswith(".html"):
                print(f"- Processing {filename}...")
                full_filename = os.path.join(directory_path, filename)
                process_file(full_filename, full_filename, process_region)


USAGE_STR = """Usage: python <name-of-this-script> [file <input-file> <output-file> | dir <dir-name>]

This script reinterprets all preformatted blocks in CoqDoc generated HTML files as Markdown and replaces them with generated HTML.
It also supports mathematical formulae.
Note that the link resolution by putting [identifier]s into brackets does not work in such blocks.

- To process a single file, use 'python gen-docs.py file <input-file> <output-file>"
- To process all HTML files recursively in a given directory, use 'python gen-docs.py dir <directory-with-html-files>"

"""
if __name__ == '__main__':
    if len(sys.argv) < 3:
        print(USAGE_STR)
        sys.exit(1)

    switch = sys.argv[1]
    if "file" == switch:
        filename_in  = sys.argv[2]
        filename_out = sys.argv[3]
        process_file(filename_in, filename_out, process_region)
    elif "dir" == switch:
        dirname = sys.argv[2]
        process_dir(dirname)
