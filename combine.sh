NAME=$1
python3 collate.py `cat docseq` > "$NAME.html" && wkhtmltopdf --enable-local-file-access --javascript-delay 24999 "$NAME.html" "$NAME.pdf"
