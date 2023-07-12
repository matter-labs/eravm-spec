from typing import List
import re
import subprocess
import sys
import pypandoc
import os

KATEX_HEADER="""
<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"
"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">
<html xmlns="http://www.w3.org/1999/xhtml">
<head>
<meta http-equiv="Content-Type" content="text/html; charset=utf-8" />
<link href="coqdoc.css" rel="stylesheet" type="text/css" />
<title>EraVM ISA specification</title>

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
</head>
<body>
"""
MATHJAX_HEADER="""
<!DOCTYPE html>
<html xmlns="http://www.w3.org/1999/xhtml" lang="" xml:lang="">
<head>
  <link href="coqdoc.css" rel="stylesheet" type="text/css" />
  <meta charset="utf-8" />
  <meta name="generator" content="pandoc" />
  <meta name="viewport" content="width=device-width, initial-scale=1.0, user-scalable=yes" />
  <title>test</title>
   <script src="https://polyfill.io/v3/polyfill.min.js?features=es6"></script>
  <script
  src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml-full.js"
  type="text/javascript"></script>
  <!--[if lt IE 9]>
    <script src="//cdnjs.cloudflare.com/ajax/libs/html5shiv/3.7.3/html5shiv-printshiv.min.js"></script>
  <![endif]-->
</head>
<body>

"""
FOOTER="""</html>"""

def adjust_links(text:str):
    no_filenames = re.sub(r"href=\"([^\"]*)html#","href=\"#", text, flags = re.DOTALL)
    no_about_blanks = re.sub(r'<a href="about:blank">[.*]<\/a>',"", no_filenames, flags = re.DOTALL)
    return no_about_blanks

def extract_body(filename:str):
    with open(filename, 'r') as file:
        data = file.read()
        match = re.search(r'<body>(.*)<div id="footer">.*</body>', data, flags = re.DOTALL)
        if match:
            return match.group(1)
        else:
            return ""

USAGE_STR="""usage"""

def collate_htmls(filenames:List[str]):
    result_html = KATEX_HEADER
    for f in filenames:
        result_html += adjust_links( extract_body(f) )

    result_html += FOOTER
    return result_html

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(USAGE_STR)
        sys.exit(1)

    files = sys.argv[1:]

    print(collate_htmls(files))
