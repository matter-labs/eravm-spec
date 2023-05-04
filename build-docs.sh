mkdir -p doc
coqdoc -toc --interpolate -utf8  -html -R src zkEVMSpec -d doc src/*.v && echo "Docs are generated in the 'doc' directory"
