from typing import List
import re
import sys
from pathlib import *
import traceback

from eravm_spec_lib import *



def evaluate_multiline_return_last(code: str):
    lines = code.strip().split('\n')

    setup_code = '\n'.join(lines[:-1])
    expression_to_evaluate = lines[-1]

    local_vars = {}

    exec(setup_code, globals(), local_vars)
    print("Evaluate: ", expression_to_evaluate)
    return eval(expression_to_evaluate, globals(), local_vars)

def evaluate_multiline_single_expr(str):
    tmp_var_name = "TMPVAR13371337"
    return evaluate_multiline_return_last(f"{tmp_var_name} = {str}\n{tmp_var_name}")

def evaluate_multiline_string(code:str):
    if code:
        if code[0] == '!':
            return evaluate_multiline_single_expr(code[1:].lstrip())
        else:
            return evaluate_multiline_return_last(code)
def header_path(file_name:str) -> Optional[Path] :
    HEADER_FILE_NAME = "_preprocess_header.py"
    header_path = Path(file_name).parents[0] / HEADER_FILE_NAME
    if header_path.exists():
        return header_path
    else:
        return None

def process_header(header_path:Path) -> None:
    with open(header_path.as_posix(), 'r') as file:
        data = file.read()
        local_vars = {}
        print(f"Processing header {header_path.as_posix()}")
        exec(data, globals(), globals())

def process_file(file_name_in:str, file_name_out:str) -> None:
    with open(file_name_in, 'r') as file:
        data = file.read()
    header = header_path(file_name_in)
    if header:
        process_header(header);

    try:
        print(f"Preprocessing file {file_name_in}")
        modified_data = re.sub(
            r'\{\{\{(.*?)\}\}\}',
            lambda match: str(evaluate_multiline_string(match.group(1))),
            data,
            flags=re.DOTALL
        )
    except:
        print(f"Exception  while preprocessing file {file_name_in}")
        traceback.print_exc()
    with open(file_name_out, 'w') as file:
        file.write(modified_data)

USAGE_STR = """Usage: python <name-of-this-script> <input-file> <output-file>

This script executes python expressions in blocks between {{{ and }}}.
"""
if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(USAGE_STR)
        sys.exit(1)

    filename_in  = sys.argv[1]
    filename_out = sys.argv[2]
    process_file(filename_in, filename_out)
