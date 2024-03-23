PYTHON=python3

# requires a custom version of CoqDoc from https://github.com/sayon/coq

COQDOC=~/repos/coq/_build/install/default/bin/coqdoc
COQLIB=~/.opam/ocaml-variants/lib/coq/
PROJECT_ROOT=`pwd`

PREPROCESSED_DIR=preprocessed

# It would be better to use `make` to generate documents faster.
rm -rf doc/*
rm -rf $PREPROCESSED_DIR
mkdir -p doc
mkdir -p $PREPROCESSED_DIR

echo "Using coqdoc at $COQDOC. This should be a custom coqdoc from the fork https://github.com/sayon/coq"


cp -r ./src/ $PREPROCESSED_DIR/src/
cp -r _CoqProject $PREPROCESSED_DIR
for f in $(find $PREPROCESSED_DIR/src -name '*.v')
do
    "$PYTHON" "$PROJECT_ROOT/scripts/preprocess-coq.py" "$f" "$f"
done


cd $PREPROCESSED_DIR
mkdir doc

coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile -j14


ALL_SRC_FILES=$(find . -name '*.v')
COQDOC_ARGS="-g -toc --parse-comments --interpolate -utf8  -html -coqlib "$COQLIB" -R src EraVM -d doc $ALL_SRC_FILES"


# Custom CoqDoc differs in two ways:
# - ignores all markdown in documentation
# - uses a different syntax for inline Coq blocks: instead of [coq code], it is [%coq code].
#   This prevents conflict with Markdown syntax for links and images.
echo "Docs are being generated in the directory " $PREPROCESSED_DIR "/doc"
echo $COQDOC $COQDOC_ARGS
"$COQDOC" $COQDOC_ARGS && echo "Docs have been generated"


cd $PROJECT_ROOT

rm -rf doc
mv $PREPROCESSED_DIR/doc .
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
"$PYTHON" "$PROJECT_ROOT/scripts/collate.py" `cat docseq` > "doc/$NAME.html"
