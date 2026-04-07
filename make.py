#!/bin/python

from mathml import Parser
from itertools import chain
from pathlib import Path
from re import compile, Match
from sys import argv

title = compile(r"^<title>(.*)</title>")
section = compile(r"^<h(.)>(.*)</h.>")
math = compile(r"<math(.*?)>(.*?)</math>")
buildpath = Path("static")
cachepath = Path(".cache")
cachepath.mkdir(exist_ok=True)
smt = Path("make.py").stat().st_mtime

def repl_math(match: Match):
	parser = Parser()
	for c in match.group(2):
		parser(c)
	return f"<math{match.group(1)}>{parser.finish()[2]}</math>"

def processarticle(f: Path) -> tuple[Path, str]:
	tit = "No title found"
	sections = []
	m = 6
	of = f.with_suffix(".html")
	cf = cachepath / f.with_suffix(".title")
	outf = buildpath / of
	mt = f.stat().st_mtime
	if outf.is_file() and cf.is_file() and smt < mt and mt < outf.stat().st_mtime and mt < cf.stat().st_mtime:
		print("Using cache for", f)
		return of, cf.read_text()
	print("Processing", f)
	l = f.read_text().splitlines(keepends=True)
	for i, x in enumerate(l):
		if mt := title.match(x):
			tit = mt.group(1)
		if ms := section.match(x):
			h = int(ms.group(1))
			m = min(m, h)
			j = len(sections)
			sections.append((h, ms.group(2)))
			l[i] = section.sub(f'<h\\1 id="{j}">\\2 <a href="#{j}">#</a></h\\1>', x, 1)
		l[i] = math.sub(repl_math, l[i])
	with cf.open("w") as fd:
		fd.write(tit)
	with outf.open("w") as fd:
		for x in l:
			fd.write(x)
			if x != "<nav>\n":
				continue
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
	return of, tit

l = Path().glob("article-*.template")
if "--stub" in argv:
	l = chain(l, Path().glob("article-*.stub"))
l = map(processarticle, sorted(l, reverse=True))

print("Processing index")
with open("index.template") as fin, open("static/index.html", "w") as fout:
	for x in fin:
		if x == "<!-- Insert dynamic content here -->\n":
			for p, t in l:
				fout.write(f'<li><a href="{p}" onclick="return IFrameScroll(this);">{t}</a></li>\n')
		else:
			fout.write(x)

if "--countdown" in argv:
	print("Processing countdown")
	with open("countdown.template") as fin, open("static/countdown.html", "w") as fout:
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
