#!/bin/python

r"""
Syntax:
whitespaces are ignored but can be used as separators
identitifiers (only alphabetic, separate at the next non alphabetic)
&htmlsymbol; (only alphabetic, final semicolon optional, some common synonyms are mapped, see word_table)
>, <, <=, >=, <=>, =>, ->, !=, ~= are shortcuts for symbols (see symbol_table)
. translates to middle dot
` becomes root (`2$ = sqrt(2), `$2 = sqrt(2), `32 = cubic root of 2)
" encloses pure text (mtext)
@ starts a group (mrow)
? starts a table
´ goes to the next cell
\ goes to the next row/line
$ ends stuff taking multiple arguments (groups, tables, roots, subscripts, superscripts)
/ in infix makes a fraction with element around
_ in infix makes the next element a subscript or under (depending on sensible rules) of the previous element
^ in infix makes the next element a superscript of over (depending on sensible rules) of the previous element
enclose in mrow to force under/over, make an empty under/over (_$ or ^$) then a new subscript/superscript to get a subscript or superscript (ex: lim_$_@n->@+&infin$$) on something which would otherwise do an under/over
"""

from enum import IntEnum
from sys import stdin, argv

# Lists html codes considered symbols, with verticality (true => underover, False => subsup)
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
	"exist": None,
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
# synonyms for html codes (put things without a name on the right here like #x2702 for black scissors)
word_table = {
	"in": "isin",
	"subset": "sub",
	"subseteq": "sube",
	"leq": "le",
	"geq": "ge",
	"neq": "ne",
	"approx": "asymp",
	"exists": "exist",
	"d": "DifferentialD",
	"Equiv": "hArr",
	"Implies": "rArr",
	"maps": "map",
	"mapsto": "map",
	"to": "rarr",
	"wedge": "and",
	"vee": "or",
	"dot": "sdot",
	"infinity": "infin",
	"inf": "infin"
}
# list of symbols starting a long symbol (shouldn't be modified)
compound_symbol = "<>-!=~"
# table of long symbols requiring a translation
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
	UNDEROVER = 7
	SUBSUP = 8
	SUBUNDER = 9
	SUPOVER = 10

underover_tag = ["underover", "under", "over"]
subsup_tag = ["subsup", "sub", "sup"]

class Parser:
	def __init__(self):
		self._desc = []
		self._stack = [(Mtag.TOP, [])]
		self._partial = []
		self._underover = None
		self._state = self._initial_state

	def _print_status(self):
		print("desc:", "".join(self._desc))
		print("partial:", "".join(self._partial))
		print("stack:")
		for x in self._stack:
			print(x[0], " ## ".join("".join(xi) for xi in x[1:]))
		print()

	def __call__(self, chr: str):
		self._state(chr)

	def _emit(self, underover: bool, *args):
		self._underover = underover
		self._partial = args
		self._state = self._infix_state

	def _hard_emit(self, _, *args):
		self._stack.pop()
		self._stack[-1][-1].extend(args)
		self._reduce(True)

	def _soft_emit(self, *args):
		self._stack.pop()
		self._emit(*args)

	# hard is a stupid name, True means next character is for sure none of the infixes, False means $
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
			case Mtag.SUPOVER:
				self._stack.pop()
				self._stack[-1][-1].extend(data)
		tag, base, su, sa = self._stack[-1]
		match len(su) != 0, len(sa) != 0:
			case True, True:
				key = 0
			case True, False:
				key = 1
			case False, True:
				key = 2
			case False, False:
				if tag is Mtag.SUBSUP:
					self._stack.pop()
					self._stack[-1][-1].extend(base)
					return self._reduce(hard)
				return emit(False,
					*(base[1:-1] if base[0] == "<mrow>" and base[-1] == "</mrow>" else base)
				)
		if tag is Mtag.UNDEROVER:
			tag = underover_tag[key]
			return emit(False, "<m", tag, ">", *base, *su, *sa, "</m", tag, ">")
		tag = subsup_tag[key]
		self._stack.pop()
		self._stack[-1][-1].extend(["<m", tag, ">", *base, *su, *sa, "</m", tag, ">"])
		self._reduce(hard)

	def _initial_state(self, chr):
		if chr.isspace():
			self._desc.append(chr)
			return
		if chr in compound_symbol:
			self._partial = [chr]
			self._state = self._compound_state
			return
		if chr.isdecimal():
			self._desc.append(chr)
			self._partial = [chr]
			self._state = self._number_state
			return
		if chr.isalpha():
			self._desc.append(chr)
			self._partial = [chr]
			self._state = self._ident_state
			return
		match chr:
			# case "*": # star?
			case ".": # middle dot
				self._desc.append("&sdot;")
				self._emit(False, "<mo>&sdot;</mo>")
			case "&": # html symbol (end on non alpha)
				self._partial = []
				self._state = self._html_state
			case "`": # mroot / msqrt
				self._desc.append("&Sqrt;")
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
				self._desc.append(chr)
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
		is_operator, self._underover = (True, html_symbols[w]) \
			if w in html_symbols else (False, False)
		w = f"&{word_table.get(w, w)};"
		self._desc.append(w)
		tag = "o" if is_operator else "i"
		self._partial = ["<m", tag, ">", w, "</m", tag, ">"]
		self._state = self._infix_state
		if chr != ";":
			self._infix_state(chr)

	def _compound_state(self, chr):
		s = self._partial[0]
		np = s + chr
		if np in symbol_table:
			self._partial = [np]
			return
		s = symbol_table.get(s, s)
		self._desc.append(s)
		self._emit(True, "<mo>", s, "</mo>")
		self._infix_state(chr)

	def _text_state(self, chr):
		if chr == '"':
			self._emit(True, "<mtext>", *elf._partial, "</mtext>")
		else:
			self._desc.append(chr)
			self._partial.append(chr)

	def _number_state(self, chr):
		if chr.isdecimal() or chr == ".":
			self._desc.append(chr)
			self._partial.append(chr)
			return
		self._emit(False, "<mn>", *self._partial, "</mn>")
		self._infix_state(chr)

	def _ident_state(self, chr):
		if chr.isalpha():
			self._desc.append(chr)
			self._partial.append(chr)
			return
		self._emit(len(self._partial) > 1, "<mi>", *self._partial, "</mi>")
		self._infix_state(chr)

	def _infix_state(self, chr):
		if chr.isspace():
			self._desc.append(chr)
			return
		self._state = self._initial_state
		partial = self._partial
		self._partial = []
		if chr == "/":
			self._desc.append(chr)
			self._stack.append((Mtag.FRAC, partial))
			return
		if chr not in ("^", "_"):
			self._stack[-1][-1].extend(partial)
			self._reduce(True)
			return self._initial_state(chr)
		self._desc.append(chr)
		toptag = self._stack[-1][0]
		newtag = Mtag.SUBUNDER if chr == "_" else Mtag.SUPOVER
		if toptag not in (Mtag.SUBUNDER, Mtag.SUPOVER):
			parenttag = Mtag.UNDEROVER if self._underover else Mtag.SUBSUP
			self._stack.append((parenttag, partial, [], []))
			self._stack.append((newtag, []))
			return
		# special cases SUBUNDER/SUPOVER: does not associate the way you think
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
		parenttag = (subsup_tag if toptag is Mtag.SUBSUP else underover_tag)[key]
		partial = ["<m", parenttag, ">", *base, *su, *sa, "</m", parenttag, ">"]
		self._stack.append((Mtag.SUBSUP, partial, [], []))
		self._stack.append((newtag, []))

	def finish(self) -> str:
		self._stack[-1][-1].extend(self._partial)
		self._partial = []
		while len(self._stack) > 1:
			self._reduce(True) # faster and doesn't put stuff in _partial
			if len(self._stack) == 1:
				break
			self._reduce(False) # safer because it always reduces
			self._stack[-1][-1].extend(self._partial)
			self._partial = []
		return "".join(self._desc), "".join(self._stack[0][1])

parser = Parser()

file = open(argv[1]) if len(argv) > 1 else stdin

while chin := file.read(1):
	parser(chin)

desc, xml = parser.finish()
print(f"<math displaystyle=true title=\"", desc, "\">", xml, "</math>", sep="")
