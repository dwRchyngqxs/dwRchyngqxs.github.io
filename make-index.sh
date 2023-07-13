#!/bin/sh

echo -n 's@^<!-- Insert dynamic content here -->$@' > sed-command
for n in `find -name 'article-*.html' | sort -r`; do
  echo -n '<li><a href="'$n'">' >> sed-command
  sed -n 's@^<title>\(.*\)</title>$@\1</a></li>\\@p' "$n" >> sed-command
done
echo '@' >> sed-command
sed --file=sed-command index.template > index.html
rm sed-command
git add index.html
