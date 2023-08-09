#!/bin/python

import pathlib
import re

title = re.compile(r"^<title>(.*)</title>")
section = re.compile(r"^<h(.)>(.*)</h.>")

def processarticle(f):
	tit = "No title found"
	sections = []
	l = []
	m = 6
	with open(f) as fd:
		l = fd.readlines()
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
	with open(f, "w") as fd:
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
	return (f, tit)

l = list(pathlib.Path().glob("article-*.template"))
l.sort(reverse=True)
l = map(processarticle, l)
with open("index.template") as fin, open("index.html", "w") as fout:
	for x in fin:
		if x == "<!-- Insert dynamic content here -->\n":
			for p, t in l:
				fout.write(f'<li><a href="{p}" onclick="return IFrameScroll(this);">{t}</a></li>\n')
			continue
		fout.write(x)
