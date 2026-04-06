#!/bin/python

from itertools import chain
from pathlib import Path
from re import compile
from sys import argv

title = compile(r"^<title>(.*)</title>")
section = compile(r"^<h(.)>(.*)</h.>")
buildpath = Path("static")

def processarticle(f):
	print("Processing", f)
	tit = "No title found"
	sections = []
	m = 6
	l = f.read_text().splitlines(keepends=True)
	for i, x in enumerate(l):
		mt = title.match(x)
		if mt:
			tit = mt.group(1)
		ms = section.match(x)
		if ms:
			h = int(ms.group(1))
			m = min(m, h)
			j = len(sections)
			sections.append((h, ms.group(2)))
			l[i] = section.sub(f'<h\\1 id="{j}">\\2 <a href="#{j}">#</a></h\\1>', x, 1)
	f = f.with_suffix(".html")
	with open(buildpath / f, "w") as fd:
		for x in l:
			fd.write(x)
			if x == "<nav>\n":
				oh = m - 1
				for i, (h, t) in enumerate(sections):
					for _ in range(oh, h):
						fd.write("<ul>\n")
					for _ in range(h, oh):
						fd.write("</ul>\n")
					oh = h
					fd.write(f'<li><a href="#{i}">{t}</a></li>\n')
				for _ in range(m - 1, oh):
					fd.write("</ul>\n")
	return f, tit

l = Path().glob("article-*.template")
if len(argv) > 1:
	l = chain(l, Path().glob("article-*.stub"))
l = map(processarticle, sorted(l, reverse=True))

with open("index.template") as fin, open("static/index.html", "w") as fout:
	print("Processing index")
	for x in fin:
		if x == "<!-- Insert dynamic content here -->\n":
			for p, t in l:
				fout.write(f'<li><a href="{p}" onclick="return IFrameScroll(this);">{t}</a></li>\n')
		else:
			fout.write(x)

with open("countdown.template") as fin, open("static/countdown.html", "w") as fout:
	print("Processing countdown")
	for x in fin:
		if x == "<!-- Insert short sounds here -->\n":
			for p in Path().glob("short_sounds/*.mp3"):
				fout.write(f'\t\t"{p}",\n')
		elif x == "<!-- Insert long sounds here -->\n":
			for p in Path().glob("long_sounds/*.mp3"):
				fout.write(f'\t\t"{p}",\n')
		else:
			fout.write(x)

print("Done")
