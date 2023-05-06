mkdir -p doc
coqdoc -toc --interpolate -utf8  -html -R src zkEVMSpec -d doc src/*.v && echo "Docs are generated in the 'doc' directory"
# cd doc
for file in `find doc -name '*.html'`
do
./prepare.sh "$file"
done
cp -f coqdoc.css doc
