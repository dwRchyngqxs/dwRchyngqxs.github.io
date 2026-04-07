#!/bin/python

r"""
Syntax:
whitespace are ignored but can be used as separators
identitifiers (only alphabetic, separates at the next non alphabetic)
&htmlsymbol; (only alphabetic, final semicolon optional, some common synonyms are mapped, see word_table)
>, <, <=, >=, <=>, =>, ->, !=, ~= are shortcuts for symbols (see symbol_table)
. translates to middle dot
` becomes root (`2$ = sqrt(2), `$2 = sqrt(2), `32 = cubic root of 2)
" encloses pure text (mtext)
@ starts a group (mrow)
? starts a table
´ goes to the next cell
\ goes to the next row/line
$ ends stuff taking multiple arguments (groups, tables, roots, subscripts, subperscripts)
/ in infix makes a fraction with element around
_ in infix makes the next element a subscript or under (depending on sensible rules) of the previous element
^ in infix makes the next element a superscript of above (depending on sensible rules) of the previous element
enclose in mrow to force under/above, make an empty under/above (_$ or ^$) then a new subscript/superscript to get a subscript or superscript (ex: lim_$_@n->@+&infin$$) on something which would otherwise do an under/above
"""

from enum import IntEnum
from sys import stdin

html_symbols = {
	"isin": True,
	"notin": True,
	"sub": True,
	"sube": True,
	"lt": True,
	"gt": True,
	"le": True,
	"ge": True,
	"ne": True,
	"sim": True,
	"asymp": True,
	"equiv": True,
	"coloneq": None,
	"forall": None,
	"exists": None,
	"bigcup": True,
	"bigcap": True,
	"sum": True,
	"prod": True,
	"int": False,
	"DifferentialD": None,
	"rarr": None,
	"map": None,
	"rArr": True,
	"hArr": True,
	"cup": None,
	"cap": None,
	"and": None,
	"or": None,
	"sdot": None
}
word_table = {
	"in": "isin",
	"subset": "sub",
	"subseteq": "sube",
	"leq": "le",
	"geq": "ge",
	"neq": "ne",
	"approx": "asymp",
	"d": "DifferentialD",
	"Equiv": "hArr",
	"Implies": "rArr",
	"maps": "map",
	"mapsto": "map",
	"to": "rarr",
	"wedge": "and",
	"vee": "or",
	"dot": "sdot"
}
compound_symbol = "<>-!=~"
symbol_table = {
	">": "&gt;",
	">=": "&ge;",
	"<": "&lt;",
	"<=": "&le;",
	"<=>": "&hArr;",
	"->": "&rarr;",
	"!=": "&ne;",
	"=>": "&rArr;",
	"~=": "&approx;",
}

class Mtag(IntEnum):
	TOP = 0
	ROW = 1
	ROOT = 2
	ROOT2 = 3
	SQRT = 4
	TABLE = 5
	FRAC = 6
	UNDERABOVE = 7
	SUBSUP = 8
	SUBUNDER = 9
	SUPABOVE = 10

aboveunder_tag = ["aboveunder", "under", "above"]
subsup_tag = ["subsup", "sub", "sup"]

class Parser:
	def __init__(self):
		self._stack = [(Mtag.TOP, [])]
		self._partial = []
		self._underabove = None
		self._state = self._initial_state

	def __call__(self, chr: str):
		self._state(chr)

	def _emit(self, underabove: bool, *args):
		self._underabove = underabove
		self._partial = args
		self._state = self._infix_state

	def _hard_emit(self, _, *args):
		self._stack.pop()
		self._stack[-1][-1].extend(args)
		self._reduce(True)

	def _soft_emit(self, *args):
		self._stack.pop()
		self._emit(*args)

	def _reduce(self, hard: bool):
		emit = self._hard_emit if hard else self._soft_emit
		restack = (lambda *_: ()) if hard else self._soft_emit

		tag, data = self._stack[-1]
		match tag:
			case Mtag.TOP:
				return
			case Mtag.ROW:
				restack(True, "<mrow>", *data, "</mrow>")
				return
			case Mtag.ROOT:
				return emit(False, "<mroot>", *data, "</mroot>")
			case Mtag.ROOT2:
				if hard:
					self._stack.append((Mtag.ROOT, data))
				else:
					self._emit(False, "<msqrt>", *data, "</msqrt>")
				return
			case Mtag.SQRT:
				return emit(False, "<msqrt>", *data, "</msqrt>")
			case Mtag.TABLE:
				restack(True, "<mtable><mtr><mtd>", *data, "</mtd></mtr></mtable>")
				return
			case Mtag.FRAC:
				return emit(True, "<mfrac>", *data, "</mfrac>")
			case Mtag.SUBUNDER:
				self._stack.pop()
				self._stack[-1][-2].extend(data)
			case Mtag.SUPABOVE:
				self._stack.pop()
				self._stack[-1][-1].extend(data)
		tag, base, su, sa = self._stack.pop()
		match len(su) != 0, len(sa) != 0:
			case True, True:
				key = 0
			case True, False:
				key = 1
			case False, True:
				key = 2
			case False, False:
				if tag is Mtag.SUBSUP:
					self._stack[-1][-1].extend(base)
					return self._reduce(hard)
				return emit(False,
					*(base[1:-1] if base[0] == "<mrow>" and base[-1] == "</mrow>" else base)
				)
		if tag is Mtag.UNDERABOVE:
			tag = aboveunder_tag[key]
			return emit(False, "<m", tag, ">", *base, *su, *sa, "</m", tag, ">")
		tag = subsup_tag[key]
		self._stack[-1][-1].extend(["<m", tag, ">", *base, *su, *sa, "</m", tag, ">"])
		self._reduce(hard)

	def _initial_state(self, chr):
		if chr.isspace():
			return
		if chr in compound_symbol:
			self._partial = [chr]
			self._state = self._compound_state
			return
		if chr.isdecimal():
			self._partial = [chr]
			self._state = self._number_state
			return
		if chr.isalpha():
			self._partial = [chr]
			self._state = self._ident_state
			return
		match chr:
			# case "*": # star?
			case ".": # middle dot
				self._emit(False, "<mo>&sdot;</mo>")
			case "&": # html symbol (end on non alpha)
				self._partial = []
				self._state = self._html_state
			case "`": # mroot / msqrt
				self._state = self._root_state
			case '"': # mtext
				self._state = self._text_state
			case "@": # mrow
				self._stack.append((Mtag.ROW, []))
			case "?": # mtable
				self._stack.append((Mtag.TABLE, []))
			case "\\": # table new line
				self._stack[-1][-1].append("</mtd></mtr><mtr><mtd>")
			case "´": # table new column
				self._stack[-1][-1].append("</mtd><mtd>")
			case "$": # state end
				self._reduce(False)
			case _:
				self._emit(False, "<mo>", chr, "</mo>")

	def _root_state(self, chr):
		if chr.isspace():
			return
		self._state = self._initial_state
		if chr == "$":
			self._stack.append((Mtag.SQRT, []))
			return
		self._stack.append((Mtag.ROOT2, []))
		self._initial_state(chr)

	def _html_state(self, chr):
		if chr.isalpha():
			self._partial.append(chr)
			return
		w = "".join(self._partial)
		is_operator, self._underabove = (True, html_symbols[w]) \
			if w in html_symbols else (False, False)
		tag = "o" if is_operator else "i"
		self._partial = ["<m", tag, ">", "&", word_table.get(w, w), ";", "</m", tag, ">"]
		self._state = self._infix_state
		if chr != ";":
			self._infix_state(chr)

	def _compound_state(self, chr):
		s = self._partial[0]
		np = s + chr
		if np in symbol_table:
			self._partial = [np]
			return
		self._emit(True, "<mo>", symbol_table.get(s, s), "</mo>")
		self._infix_state(chr)

	def _text_state(self, chr):
		if chr == '"':
			self._emit(True, "<mtext>", *self._partial, "</mtext>")
		else:
			self._partial.append(chr)

	def _number_state(self, chr):
		if chr.isdecimal() or chr == ".":
			self._partial.append(chr)
			return
		self._emit(False, "<mn>", *self._partial, "</mn>")
		self._infix_state(chr)

	def _ident_state(self, chr):
		if chr.isalpha():
			self._partial.append(chr)
			return
		self._emit(len(self._partial) > 1, "<mi>", *self._partial, "</mi>")
		self._infix_state(chr)

	def _infix_state(self, chr):
		if chr.isspace():
			return
		self._state = self._initial_state
		partial = self._partial
		self._partial = []
		if chr == "/":
			self._stack.append((Mtag.FRAC, partial))
			return
		if chr not in ("^", "_"):
			self._stack[-1][-1].extend(partial)
			self._reduce(True)
			return self._initial_state(chr)
		toptag = self._stack[-1][0]
		newtag = Mtag.SUBUNDER if chr == "_" else Mtag.SUPABOVE
		if toptag not in (Mtag.SUBUNDER, Mtag.SUPABOVE):
			parenttag = Mtag.UNDERABOVE if self._underabove else Mtag.SUBSUP
			self._stack.append((parenttag, partial, [], []))
			self._stack.append((newtag, []))
			return
		# special cases SUBUNDER/SUPABOVE: does not associate the way you think
		self._stack.pop()
		self._stack[-1][-2 if toptag is Mtag.SUBUNDER else -1].extend(partial)
		if not self._stack[-1][-2 if newtag is Mtag.SUBUNDER else -1]:
			self._stack.append((newtag, []))
			return
		# reduce
		toptag, su, sa = self._stack.pop()
		match su, sa:
			case True, True:
				key = 0
			case True, False:
				key = 1
			case False, True:
				key = 2
			case False, False:
				assert False
		parenttag = (subsup_tag if toptag is Mtag.SUBSUP else aboveunder_tag)[key]
		partial = ["<m", parenttag, ">", *base, *su, *sa, "</m", parenttag, ">"]
		self._stack.append((Mtag.SUBSUP, partial, [], []))
		self._stack.append((newtag, []))

	def finish(self) -> str:
		while self._stack[-1][0] is not Mtag.TOP:
			self._reduce(True) # faster
			if self._stack[-1][0] is Mtag.TOP:
				break
			self._reduce(False) # safer
			self._stack[-1][-1].extend(self._partial)
		return "".join(self._stack[0][1])

parser = Parser()

while chin := stdin.read(1):
	parser(chin)

print(parser.finish())
