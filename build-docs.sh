PYTHON=python3
# requires a custom version of CoqDoc from https://github.com/sayon/coq
COQDOC=/Users/sayon/repos/coq/_build/install/default/bin/coqdoc
COQLIB=/Users/sayon/.opam/ocaml-variants/lib/coq/
# Prince is a tool to transform html->pdf.
# wkhtmltopdf unfortunately does not work well with mathjax/katex
# "print to pdf" does not retain internal links
PRINCE=~/distr/usr/local/bin/prince
rm -rf doc/*
mkdir -p doc
echo "Using coqdoc at $COQDOC"
$COQDOC -toc --parse-comments --interpolate -utf8  -html -coqlib $COQLIB -R src EraVM -d doc `find src -name '*.v'` && echo "Docs are generated in the 'doc' directory"
cp -fr img coqdoc.css doc
for f in `find doc -name '*.html'`
do
    $PYTHON process-docs.py file "$f" "$f"
done

NAME=spec
python3 collate.py `cat docseq` > "doc/$NAME.html"
#wkhtmltopdf --enable-local-file-access --no-stop-slow-scripts --enable-javascript --javascript-delay 60000  "$NAME.html" "$NAME.pdf"

# Prince is capable of collating multiple files together, but it is faster to use a script `collate.py`. Additionally, `collate.py` cuts out some unwanted parts
"$PRINCE" --raster-dpi=300 -j "doc/$NAME.html" -o "doc/$NAME.pdf"
