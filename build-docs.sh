PYTHON=python3
COQDOC=/Users/sayon/repos/coq/_build/install/default/bin/coqdoc
rm -rf doc
mkdir -p doc
echo "Using coqdoc at $COQDOC"
$COQDOC -toc --parse-comments --interpolate -utf8  -html -R src zkEVMSpec -d doc `find src -name '*.v'` && echo "Docs are generated in the 'doc' directory"
$PYTHON process-docs.py dir doc && echo "Markdown in docs is processed"
cp -f coqdoc.css doc
