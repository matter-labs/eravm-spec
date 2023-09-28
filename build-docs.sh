PYTHON=python3

# requires a custom version of CoqDoc from https://github.com/sayon/coq

COQDOC=~/repos/coq/_build/install/default/bin/coqdoc
COQLIB=~/.opam/ocaml-variants/lib/coq/
PROJECT_ROOT=`pwd`
ALL_SRC_FILES=$(find src -name '*.v')
COQDOC_ARGS="-g -toc --parse-comments --interpolate -utf8  -html -coqlib "$COQLIB" -R src EraVM -d doc $ALL_SRC_FILES"

# It would be better to use `make` to generate documents faster.
rm -rf doc/*
mkdir -p doc
echo "Using coqdoc at $COQDOC. This should be a custom coqdoc from the fork https://github.com/sayon/coq"

# Custom CoqDoc differs in two ways:
# - ignores all markdown in documentation
# - uses a different syntax for inline Coq blocks: instead of [coq code], it is [%coq code].
#   This prevents conflict with Markdown syntax for links and images.
"$COQDOC" $COQDOC_ARGS && echo "Docs are generated in the 'doc' directory"
cp -fr img coqdoc.css doc

# The script 'process-docs' passes each individual coqdoc block in HTML file
# through pandoc to convert its Markdown to HTML.
for f in `find doc -name '*.html'`
do
    "$PYTHON" "$PROJECT_ROOT/scripts/process-docs.py" file "$f" "$f"
done

# `collate` forms a single huge HTML file from everything available in the spec.
# It gets the ordered list of source files from the file `docseq`
NAME=spec
python3 "$PROJECT_ROOT/scripts/collate.py" `cat docseq` > "doc/$NAME.html"
