PYTHON=python3

rm -rf doc
mkdir -p doc
coqdoc -toc --interpolate -utf8  -html -R src zkEVMSpec -d doc src/*.v && echo "Docs are generated in the 'doc' directory"
$PYTHON process-docs.py dir doc && echo "Markdown in docs is processed"
cp -f coqdoc.css doc
