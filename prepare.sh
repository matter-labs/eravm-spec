NAME="$1"
BKP="$NAME.old"
echo "Processing $NAME, backed up as $BKP"
cp -f "$NAME" "$BKP"
sed -i.bak -E 's/<\/?pre>//g' "$BKP"  
echo "pandoc... "
timeout 10 pandoc -f markdown-smart -t html "$BKP"  | tail --lines=+3  > "$NAME" && rm "$BKP"
echo "pandoc ok"
