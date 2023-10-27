// Code generated by goyacc -l -p TPTP -o ./parser/tptp_6.3.0.go ./parser/tptp_6.3.0.y. DO NOT EDIT.

package parser

import __yyfmt__ "fmt"

import (
	"fmt"
	basictypes "github.com/GoelandProver/Goeland/types/basic-types"
	"io/ioutil"
	"os"
	"unicode"
)

// Count of quantifiers (bound)
var cpt_quantif = 0

// To locate the line number of an error
var yylineno = 1

// To factorize applications to terms (functions and predicates)
type App struct {
	symb basictypes.Id
	args []basictypes.Term
} //App

// To get the final result
var res []basictypes.Statement

type TPTPSymType struct {
	yys  int
	val  string
	lstm []basictypes.Statement
	stm  basictypes.Statement
	fr   basictypes.FormulaRole
	form basictypes.Form
	term basictypes.Term
	ltrm []basictypes.Term
	vrl  []basictypes.Var
	vrb  basictypes.Var
	app  App
	id   basictypes.Id
	ls   []string
}

const EOF = 57346
const DOT = 57347
const COMMA = 57348
const COLON = 57349
const EXPONENT = 57350
const LEFT_PAREN = 57351
const RIGHT_PAREN = 57352
const LEFT_BRACKET = 57353
const RIGHT_BRACKET = 57354
const FOF = 57355
const INCLUDE = 57356
const FORALL = 57357
const EXISTS = 57358
const ARROW = 57359
const STAR = 57360
const PLUS = 57361
const SIGN = 57362
const ZERO_NUMERIC = 57363
const NUMERIC = 57364
const SLASH = 57365
const XOR = 57366
const EQUIV = 57367
const IMPLY = 57368
const LEFT_IMPLY = 57369
const NOT = 57370
const AND = 57371
const VLINE = 57372
const NOTAND = 57373
const NOTVLINE = 57374
const EQUAL = 57375
const NOT_EQUAL = 57376
const GENTZEN_ARROW = 57377
const ITE_F = 57378
const ITE_T = 57379
const LET_TF = 57380
const LET_FF = 57381
const LET_FT = 57382
const LET_TT = 57383
const DOLLAR_FOF = 57384
const DOLLAR_FOT = 57385
const LOWER_WORD = 57386
const UPPER_WORD = 57387
const SINGLE_QUOTED = 57388
const DISTINCT_OBJECT = 57389
const DOLLAR_WORD = 57390
const DOLLAR_DOLLAR_WORD = 57391
const REAL = 57392
const RATIONAL = 57393
const INTEGER = 57394

var TPTPToknames = [...]string{
	"$end",
	"error",
	"$unk",
	"EOF",
	"DOT",
	"COMMA",
	"COLON",
	"EXPONENT",
	"LEFT_PAREN",
	"RIGHT_PAREN",
	"LEFT_BRACKET",
	"RIGHT_BRACKET",
	"FOF",
	"INCLUDE",
	"FORALL",
	"EXISTS",
	"ARROW",
	"STAR",
	"PLUS",
	"SIGN",
	"ZERO_NUMERIC",
	"NUMERIC",
	"SLASH",
	"XOR",
	"EQUIV",
	"IMPLY",
	"LEFT_IMPLY",
	"NOT",
	"AND",
	"VLINE",
	"NOTAND",
	"NOTVLINE",
	"EQUAL",
	"NOT_EQUAL",
	"GENTZEN_ARROW",
	"ITE_F",
	"ITE_T",
	"LET_TF",
	"LET_FF",
	"LET_FT",
	"LET_TT",
	"DOLLAR_FOF",
	"DOLLAR_FOT",
	"LOWER_WORD",
	"UPPER_WORD",
	"SINGLE_QUOTED",
	"DISTINCT_OBJECT",
	"DOLLAR_WORD",
	"DOLLAR_DOLLAR_WORD",
	"REAL",
	"RATIONAL",
	"INTEGER",
}

var TPTPStatenames = [...]string{}

const TPTPEofCode = 1
const TPTPErrCode = 2
const TPTPInitialStackSize = 16

/*  start  of  programs  */

// Hand-written lexer

type TPTPLex struct {
	s   string
	pos int
}

// Skips comments
// Returns 0 if there is nothing more to read, 1 otherwise
func (l *TPTPLex) SkipComments() int {
	if l.pos == len(l.s) {
		return 0
	} //if
	c := rune(l.s[l.pos])
	if c == '%' {
		for c != '\n' {
			l.pos += 1
			if l.pos == len(l.s) {
				return 0
			} //if
			c = rune(l.s[l.pos])
		} //for
		yylineno += 1
		l.pos += 1
		if l.pos == len(l.s) {
			return 0
		} //if
	} //if
	return 1
} //SkipComments

// Skips spaces, line feeds, etc.
// Returns 0 if there is nothing more to read, 1 otherwise
func (l *TPTPLex) SkipSpaces() int {
	var c rune = ' '
	for c == ' ' || c == '\n' || c == '\r' || c == '\t' {
		if l.pos == len(l.s) {
			return 0
		} //if
		c = rune(l.s[l.pos])
		if c == ' ' || c == '\n' || c == '\r' || c == '\t' {
			l.pos += 1
			if c == '\n' {
				yylineno += 1
			} //if
		} //if
	} //for
	return 1
} //SkipSpaces

// Skips comments and spaces, line feeds, etc.
// Returns 0 if there is nothing more to read, 1 otherwise
func (l *TPTPLex) SkipCommentsAndSpaces() int {
	stop := false
	for !stop {
		before := l.pos
		res := l.SkipComments()
		if res == 0 {
			return 0
		} //if
		stop = (before == l.pos)
		before = l.pos
		res = l.SkipSpaces()
		if res == 0 {
			return 0
		} //if
		stop = stop && (before == l.pos)
	} //for
	return 1
} //SkipCommentsAndSpaces

// Checks if name is a keyword
func IsKeyword(name string) (int, bool) {
	switch name {
	case "fof":
		return FOF, false
	case "include":
		return INCLUDE, false
	default:
		return 0, true
	} //switch
} //IsKeyword

// Checks if the next token is a upper/lower word or a keyword
// Returns the token if recognized, 0 otherwise (something remains to be read)
func (l *TPTPLex) Word(lval *TPTPSymType) int {
	c := rune(l.s[l.pos])
	name := string(c)
	if unicode.IsUpper(c) || unicode.IsLower(c) {
		var token int
		if unicode.IsUpper(c) {
			token = UPPER_WORD
		} else /*if*/ {
			token = LOWER_WORD
		} //else
		l.pos += 1
		if l.pos == len(l.s) {
			lval.val = name
			return token
		} //if
		c = rune(l.s[l.pos])
		for unicode.IsLetter(c) || unicode.IsDigit(c) || c == '_' {
			name = name + string(c)
			l.pos += 1
			if l.pos == len(l.s) {
				kwd, err := IsKeyword(name)
				if err {
					lval.val = name
					return token
				} else /*if*/ {
					return kwd
				} //else
			} //if
			c = rune(l.s[l.pos])
		} //for
		kwd, err := IsKeyword(name)
		if err || c != '(' {
			lval.val = name
			return token
		} else /*if*/ {
			return kwd
		} //else
	} else if c == '\'' {
		l.pos += 1
		c = rune(l.s[l.pos])
		sq_quoted := ""
		for isSqChar(c) || c == '\\' {
			if c == '\\' {
				l.pos += 1
				c = rune(l.s[l.pos])
				if c == '\\' || c == '\'' {
					sq_quoted += string('\\' + c)
				}
			} else {
				sq_quoted += string(c)
			}
			l.pos += 1
			// ... Si y'a des bugs, voir ici
			c = rune(l.s[l.pos])
		}
		l.pos += 1
		c = rune(l.s[l.pos])
		lval.val = sq_quoted
		return SINGLE_QUOTED
	} else if c == '"' {
		l.pos += 1
		c = rune(l.s[l.pos])
		sq_quoted := ""
		for isDoChar(c) || c == '\\' {
			if c == '\\' {
				l.pos += 1
				c = rune(l.s[l.pos])
				if c == '\\' || c == '"' {
					sq_quoted += string('\\' + c)
				}
			} else {
				sq_quoted += string(c)
			}
			l.pos += 1
			// ... Si y'a des bugs, voir ici
			c = rune(l.s[l.pos])
		}
		l.pos += 1
		c = rune(l.s[l.pos])
		lval.val = sq_quoted
		return DISTINCT_OBJECT
	} else if unicode.IsDigit(c) {
		tmp := string(c)
		l.pos += 1
		c = rune(l.s[l.pos])
		for unicode.IsDigit(c) {
			tmp += string(c)
			l.pos += 1
			c = rune(l.s[l.pos])
		}
		lval.val = tmp
		return NUMERIC
	} else {
		return 0
	} //else
} //Word

// 40-46, 50-133, 135-176 et \\ ou \'
//32-38 40-91 93-126
func isSqChar(c rune) bool {
	ascii := int(c)
	return (ascii >= 32 && ascii <= 38) || (ascii >= 40 && ascii <= 91) || (ascii >= 93 && ascii <= 126)
}

func isDoChar(c rune) bool {
	ascii := int(c)
	return (ascii >= 32 && ascii <= 33) || (ascii >= 35 && ascii <= 91) || (ascii >= 93 && ascii <= 126)
}

// Checks if the next token is a special word
// Returns the token if recognized, 0 otherwise
func (l *TPTPLex) SpecialWord(lval *TPTPSymType) int {
	c := l.s[l.pos]
	l.pos += 1
	switch c {
	case '.':
		return DOT
	case ',':
		return COMMA
	case ':':
		return COLON
	case '(':
		return LEFT_PAREN
	case ')':
		return RIGHT_PAREN
	case '[':
		return LEFT_BRACKET
	case ']':
		return RIGHT_BRACKET
	case '+', '-':
		lval.val = string(c)
		return SIGN
	case '0':
		return ZERO_NUMERIC
	case '/':
		return SLASH
	case 'e', 'E':
		return EXPONENT
	case '!':
		if l.pos == len(l.s) {
			cpt_quantif++
			return FORALL
		} else /*if*/ {
			c = l.s[l.pos]
			if c == '=' {
				l.pos += 1
				return NOT_EQUAL
			} else /*if*/ {
				cpt_quantif++
				return FORALL
			} //else
		} //else
	case '?':
		cpt_quantif++
		return EXISTS
	case '~':
		if l.pos == len(l.s) {
			return NOT
		} else /*if*/ {
			c = l.s[l.pos]
			switch c {
			case '&':
				l.pos += 1
				return NOTAND
			case '|':
				l.pos += 1
				return NOTVLINE
			default:
				return NOT
			} //switch
		} //else
	case '&':
		return AND
	case '|':
		return VLINE
	case '=':
		if l.pos == len(l.s) {
			return EQUAL
		} else /*if*/ {
			c = l.s[l.pos]
			if c == '>' {
				l.pos += 1
				return IMPLY
			} else /*if*/ {
				return EQUAL
			} //else
		} //else
	case '<':
		if l.pos == len(l.s) {
			return 0
		} else /*if*/ {
			c = l.s[l.pos]
			if c == '=' {
				l.pos += 1
				if l.pos == len(l.s) {
					return LEFT_IMPLY
				} else /*if*/ {
					c = l.s[l.pos]
					if c == '>' {
						l.pos += 1
						return EQUIV
					} else /*if*/ {
						return LEFT_IMPLY
					} //else
				} //else
			} else /*if*/ if c == '~' {
				l.pos += 1
				if l.pos == len(l.s) {
					return 0
				} else /*if*/ {
					c = l.s[l.pos]
					if c == '>' {
						l.pos += 1
						return XOR
					} //if
				} //else
			} //else
		} //else
		return 0
	case '$':
		if l.pos == len(l.s) {
			return 0
		} else /*if*/ {
			token := l.Word(lval)
			if token == LOWER_WORD {
				if lval.val == "fot" {
					return DOLLAR_FOT
				} else if lval.val == "true" || lval.val == "false" {
					return DOLLAR_WORD
				}
			} else if token == FOF {
				return DOLLAR_FOF
			} //if
		}

		//else
	} //switch
	return 0
} //SpecialWord

// Main lexer
func (l *TPTPLex) Lex(lval *TPTPSymType) int {
	// Skip comments and spaces, line feeds, etc.
	res := l.SkipCommentsAndSpaces()
	if res == 0 {
		return 0
	} //if
	// Keywords and names
	token := l.Word(lval)
	if token != 0 {
		return token
	} //if
	// Special words
	token = l.SpecialWord(lval)
	if token != 0 {
		return token
	} //if
	return 0
} //Lex

func (l *TPTPLex) Error(s string) {
	fmt.Printf("Syntax error, line %d: %s\n", yylineno, s)
} //Error

func check(e error) {
	if e != nil {
		fmt.Printf("Error : %v\n", e)
		os.Exit(1)
	}
} //check

func ParseMain(fn string) ([]basictypes.Statement, int) {
	dat, err := ioutil.ReadFile(fn)
	check(err)
	TPTPParse(&TPTPLex{s: string(dat)})
	return res, cpt_quantif
} //ParseMain

var TPTPExca = [...]int{
	-1, 1,
	1, -1,
	-2, 0,
	-1, 58,
	33, 52,
	34, 52,
	-2, 46,
}

const TPTPPrivate = 57344

const TPTPLast = 250

var TPTPAct = [...]int{
	42, 158, 39, 147, 115, 145, 20, 142, 24, 67,
	13, 66, 62, 33, 69, 40, 68, 136, 58, 95,
	77, 15, 57, 48, 75, 96, 159, 34, 29, 51,
	52, 101, 100, 149, 78, 23, 25, 148, 150, 149,
	122, 15, 53, 78, 23, 25, 122, 157, 15, 78,
	23, 25, 23, 25, 99, 78, 23, 25, 17, 66,
	18, 73, 60, 25, 94, 172, 83, 17, 66, 18,
	73, 123, 124, 17, 66, 18, 73, 123, 124, 17,
	66, 18, 73, 8, 7, 29, 164, 125, 126, 127,
	128, 129, 130, 131, 132, 116, 134, 135, 118, 104,
	120, 70, 119, 103, 21, 23, 25, 162, 37, 122,
	137, 137, 113, 16, 144, 151, 138, 35, 98, 140,
	140, 140, 79, 139, 141, 143, 97, 31, 17, 14,
	18, 183, 116, 16, 22, 118, 182, 120, 108, 119,
	16, 107, 27, 161, 22, 180, 26, 165, 133, 111,
	82, 160, 167, 156, 22, 102, 105, 11, 171, 169,
	10, 22, 109, 174, 178, 116, 116, 176, 118, 118,
	120, 120, 119, 119, 179, 181, 137, 184, 155, 185,
	140, 177, 170, 116, 175, 140, 118, 173, 120, 143,
	119, 89, 86, 87, 88, 166, 93, 92, 91, 90,
	163, 154, 85, 38, 36, 28, 152, 110, 30, 2,
	121, 117, 114, 9, 168, 153, 112, 84, 64, 63,
	65, 61, 59, 56, 55, 54, 47, 46, 45, 50,
	49, 44, 43, 41, 32, 76, 146, 81, 106, 80,
	74, 19, 72, 71, 12, 5, 6, 4, 3, 1,
}

var TPTPPact = [...]int{
	70, -1000, -1000, 70, -1000, -1000, -1000, 151, 148, -1000,
	-36, 84, 136, -1000, 199, -1000, -1000, -1000, -1000, -1000,
	-1000, 31, -1000, -1000, -1000, -1000, 203, 116, -31, -1000,
	-1000, 84, 198, -1000, 96, 197, 14, 140, 84, 196,
	-1000, -1000, 167, -1000, -1000, -1000, -1000, -1000, 14, -11,
	-4, 115, 107, 14, -1000, -1000, -1000, -2, -1000, -1000,
	-1000, -1000, -1000, -1000, 146, -1000, -1000, -1000, -1000, -1000,
	-1000, -1000, -1000, -1000, -1000, -1000, -1000, -1000, 31, 133,
	154, -1000, 202, -1000, 139, 29, 14, 14, 14, 14,
	14, 14, 14, 14, 138, 14, 14, -34, -34, -1000,
	23, 23, 23, -1000, -1000, 41, -1000, 17, 16, 17,
	-1000, 201, 195, -1000, 171, -1000, 144, -1000, -1000, -1000,
	-1000, -1000, 35, 142, 134, -1000, -1000, -1000, -1000, -1000,
	-1000, -1000, -1000, -1000, -1000, -1000, 95, 194, 74, -1000,
	-1000, -1000, 137, 189, -1000, -1000, -1000, -1000, 11, -1000,
	-1000, -1000, -1000, -1000, 98, 29, 29, -1000, 53, 181,
	14, 23, 160, -34, 157, -1000, 23, -1000, -1000, -1000,
	-1000, 135, -1000, 29, 126, 121, 14, -1000, 14, -1000,
	-1000, -1000, -1000, -1000, -1000, -1000,
}

var TPTPPgo = [...]int{
	0, 249, 209, 248, 247, 246, 245, 117, 244, 16,
	101, 243, 242, 14, 241, 6, 122, 8, 240, 24,
	20, 239, 238, 237, 5, 236, 3, 235, 234, 2,
	15, 233, 0, 232, 231, 230, 229, 228, 227, 226,
	225, 224, 223, 222, 22, 221, 7, 17, 12, 18,
	220, 219, 218, 9, 27, 217, 216, 215, 26, 214,
	4, 212, 211, 210, 1,
}

var TPTPR1 = [...]int{
	0, 1, 2, 2, 3, 3, 4, 5, 55, 55,
	6, 6, 8, 54, 54, 28, 29, 30, 30, 31,
	31, 33, 33, 33, 33, 33, 33, 34, 34, 35,
	35, 36, 36, 32, 32, 32, 32, 37, 37, 47,
	47, 38, 38, 40, 39, 39, 41, 42, 42, 43,
	44, 44, 45, 45, 49, 49, 50, 50, 51, 52,
	48, 46, 46, 56, 57, 57, 59, 58, 58, 58,
	61, 61, 61, 61, 61, 61, 62, 63, 63, 60,
	60, 64, 64, 7, 7, 53, 53, 9, 9, 9,
	10, 10, 14, 15, 16, 16, 17, 13, 11, 11,
	18, 19, 12, 12, 27, 20, 20, 21, 22, 23,
	23, 24, 24, 25, 26,
}

var TPTPR2 = [...]int{
	0, 1, 0, 2, 1, 1, 1, 10, 0, 3,
	5, 9, 1, 1, 3, 1, 1, 1, 1, 1,
	1, 3, 3, 3, 3, 3, 3, 1, 1, 3,
	3, 3, 3, 1, 1, 1, 3, 6, 6, 1,
	3, 2, 1, 3, 1, 1, 1, 1, 1, 3,
	1, 1, 1, 1, 1, 4, 1, 1, 1, 1,
	1, 1, 3, 1, 0, 2, 1, 1, 1, 3,
	1, 1, 1, 1, 1, 1, 4, 4, 4, 2,
	3, 1, 3, 1, 1, 1, 1, 1, 1, 1,
	1, 1, 2, 1, 1, 1, 1, 1, 1, 1,
	2, 3, 1, 1, 2, 1, 1, 2, 2, 3,
	3, 1, 1, 2, 1,
}

var TPTPChk = [...]int{
	-1000, -1, -2, -3, -4, -6, -5, 14, 13, -2,
	9, 9, -8, 46, -7, -53, -10, 44, 46, -14,
	-15, 20, -16, 21, -17, 22, 10, 6, 6, -15,
	5, 11, -28, 44, -54, -7, 6, 12, 6, -29,
	-30, -31, -32, -33, -34, -37, -38, -39, 9, -35,
	-36, 15, 16, 28, -40, -41, -42, -44, -49, -43,
	48, -45, -48, -51, -52, -50, 45, -53, -9, -13,
	-10, -11, -12, 47, -18, -19, -27, -20, 20, -16,
	-21, -23, 10, -54, -55, 6, 25, 26, 27, 24,
	32, 31, 30, 29, -30, 30, 29, 11, 11, -32,
	34, 33, 9, -19, -20, 23, -22, 8, 5, 8,
	5, 10, -56, -58, -61, -60, -53, -62, -48, -9,
	-13, -63, 11, 42, 43, -32, -32, -32, -32, -32,
	-32, -32, -32, 10, -32, -32, -47, -48, -47, -44,
	-49, -44, -46, -44, -17, -24, -25, -26, 20, 22,
	22, -24, 5, -57, 6, 7, 9, 12, -64, -58,
	9, 9, 12, 6, 12, 10, 6, -26, -59, -60,
	-58, -64, 12, 6, -29, -44, 7, -47, 7, -46,
	10, -64, 10, 10, -32, -32,
}

var TPTPDef = [...]int{
	2, -2, 1, 2, 4, 5, 6, 0, 0, 3,
	0, 0, 0, 12, 0, 83, 84, 85, 86, 90,
	91, 0, 93, 94, 95, 96, 0, 0, 0, 92,
	10, 0, 0, 15, 0, 13, 0, 0, 0, 8,
	16, 17, 18, 19, 20, 33, 34, 35, 0, 27,
	28, 0, 0, 0, 42, 44, 45, 0, -2, 47,
	48, 50, 51, 54, 58, 53, 60, 59, 56, 57,
	87, 88, 89, 97, 98, 99, 102, 103, 0, 93,
	105, 106, 0, 14, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 41,
	0, 0, 0, 100, 104, 0, 107, 0, 0, 0,
	11, 0, 64, 63, 67, 68, 70, 71, 72, 73,
	74, 75, 0, 0, 0, 21, 22, 23, 24, 25,
	26, 29, 31, 36, 30, 32, 0, 39, 0, 43,
	52, 49, 0, 61, 101, 109, 111, 112, 0, 114,
	108, 110, 7, 9, 0, 0, 0, 79, 0, 81,
	0, 0, 0, 0, 0, 55, 0, 113, 65, 66,
	69, 0, 80, 0, 0, 0, 0, 40, 0, 62,
	76, 82, 77, 78, 37, 38,
}

var TPTPTok1 = [...]int{
	1,
}

var TPTPTok2 = [...]int{
	2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
	12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
	22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
	32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
	42, 43, 44, 45, 46, 47, 48, 49, 50, 51,
	52,
}

var TPTPTok3 = [...]int{
	0,
}

var TPTPErrorMessages = [...]struct {
	state int
	token int
	msg   string
}{}

/*	parser for yacc output	*/

var (
	TPTPDebug        = 0
	TPTPErrorVerbose = false
)

type TPTPLexer interface {
	Lex(lval *TPTPSymType) int
	Error(s string)
}

type TPTPParser interface {
	Parse(TPTPLexer) int
	Lookahead() int
}

type TPTPParserImpl struct {
	lval  TPTPSymType
	stack [TPTPInitialStackSize]TPTPSymType
	char  int
}

func (p *TPTPParserImpl) Lookahead() int {
	return p.char
}

func TPTPNewParser() TPTPParser {
	return &TPTPParserImpl{}
}

const TPTPFlag = -1000

func TPTPTokname(c int) string {
	if c >= 1 && c-1 < len(TPTPToknames) {
		if TPTPToknames[c-1] != "" {
			return TPTPToknames[c-1]
		}
	}
	return __yyfmt__.Sprintf("tok-%v", c)
}

func TPTPStatname(s int) string {
	if s >= 0 && s < len(TPTPStatenames) {
		if TPTPStatenames[s] != "" {
			return TPTPStatenames[s]
		}
	}
	return __yyfmt__.Sprintf("state-%v", s)
}

func TPTPErrorMessage(state, lookAhead int) string {
	const TOKSTART = 4

	if !TPTPErrorVerbose {
		return "syntax error"
	}

	for _, e := range TPTPErrorMessages {
		if e.state == state && e.token == lookAhead {
			return "syntax error: " + e.msg
		}
	}

	res := "syntax error: unexpected " + TPTPTokname(lookAhead)

	// To match Bison, suggest at most four expected tokens.
	expected := make([]int, 0, 4)

	// Look for shiftable tokens.
	base := TPTPPact[state]
	for tok := TOKSTART; tok-1 < len(TPTPToknames); tok++ {
		if n := base + tok; n >= 0 && n < TPTPLast && TPTPChk[TPTPAct[n]] == tok {
			if len(expected) == cap(expected) {
				return res
			}
			expected = append(expected, tok)
		}
	}

	if TPTPDef[state] == -2 {
		i := 0
		for TPTPExca[i] != -1 || TPTPExca[i+1] != state {
			i += 2
		}

		// Look for tokens that we accept or reduce.
		for i += 2; TPTPExca[i] >= 0; i += 2 {
			tok := TPTPExca[i]
			if tok < TOKSTART || TPTPExca[i+1] == 0 {
				continue
			}
			if len(expected) == cap(expected) {
				return res
			}
			expected = append(expected, tok)
		}

		// If the default action is to accept or reduce, give up.
		if TPTPExca[i+1] != 0 {
			return res
		}
	}

	for i, tok := range expected {
		if i == 0 {
			res += ", expecting "
		} else {
			res += " or "
		}
		res += TPTPTokname(tok)
	}
	return res
}

func TPTPlex1(lex TPTPLexer, lval *TPTPSymType) (char, token int) {
	token = 0
	char = lex.Lex(lval)
	if char <= 0 {
		token = TPTPTok1[0]
		goto out
	}
	if char < len(TPTPTok1) {
		token = TPTPTok1[char]
		goto out
	}
	if char >= TPTPPrivate {
		if char < TPTPPrivate+len(TPTPTok2) {
			token = TPTPTok2[char-TPTPPrivate]
			goto out
		}
	}
	for i := 0; i < len(TPTPTok3); i += 2 {
		token = TPTPTok3[i+0]
		if token == char {
			token = TPTPTok3[i+1]
			goto out
		}
	}

out:
	if token == 0 {
		token = TPTPTok2[1] /* unknown char */
	}
	if TPTPDebug >= 3 {
		__yyfmt__.Printf("lex %s(%d)\n", TPTPTokname(token), uint(char))
	}
	return char, token
}

func TPTPParse(TPTPlex TPTPLexer) int {
	return TPTPNewParser().Parse(TPTPlex)
}

func (TPTPrcvr *TPTPParserImpl) Parse(TPTPlex TPTPLexer) int {
	var TPTPn int
	var TPTPVAL TPTPSymType
	var TPTPDollar []TPTPSymType
	_ = TPTPDollar // silence set and not used
	TPTPS := TPTPrcvr.stack[:]

	Nerrs := 0   /* number of errors */
	Errflag := 0 /* error recovery flag */
	TPTPstate := 0
	TPTPrcvr.char = -1
	TPTPtoken := -1 // TPTPrcvr.char translated into internal numbering
	defer func() {
		// Make sure we report no lookahead when not parsing.
		TPTPstate = -1
		TPTPrcvr.char = -1
		TPTPtoken = -1
	}()
	TPTPp := -1
	goto TPTPstack

ret0:
	return 0

ret1:
	return 1

TPTPstack:
	/* put a state and value onto the stack */
	if TPTPDebug >= 4 {
		__yyfmt__.Printf("char %v in %v\n", TPTPTokname(TPTPtoken), TPTPStatname(TPTPstate))
	}

	TPTPp++
	if TPTPp >= len(TPTPS) {
		nyys := make([]TPTPSymType, len(TPTPS)*2)
		copy(nyys, TPTPS)
		TPTPS = nyys
	}
	TPTPS[TPTPp] = TPTPVAL
	TPTPS[TPTPp].yys = TPTPstate

TPTPnewstate:
	TPTPn = TPTPPact[TPTPstate]
	if TPTPn <= TPTPFlag {
		goto TPTPdefault /* simple state */
	}
	if TPTPrcvr.char < 0 {
		TPTPrcvr.char, TPTPtoken = TPTPlex1(TPTPlex, &TPTPrcvr.lval)
	}
	TPTPn += TPTPtoken
	if TPTPn < 0 || TPTPn >= TPTPLast {
		goto TPTPdefault
	}
	TPTPn = TPTPAct[TPTPn]
	if TPTPChk[TPTPn] == TPTPtoken { /* valid shift */
		TPTPrcvr.char = -1
		TPTPtoken = -1
		TPTPVAL = TPTPrcvr.lval
		TPTPstate = TPTPn
		if Errflag > 0 {
			Errflag--
		}
		goto TPTPstack
	}

TPTPdefault:
	/* default state action */
	TPTPn = TPTPDef[TPTPstate]
	if TPTPn == -2 {
		if TPTPrcvr.char < 0 {
			TPTPrcvr.char, TPTPtoken = TPTPlex1(TPTPlex, &TPTPrcvr.lval)
		}

		/* look through exception table */
		xi := 0
		for {
			if TPTPExca[xi+0] == -1 && TPTPExca[xi+1] == TPTPstate {
				break
			}
			xi += 2
		}
		for xi += 2; ; xi += 2 {
			TPTPn = TPTPExca[xi+0]
			if TPTPn < 0 || TPTPn == TPTPtoken {
				break
			}
		}
		TPTPn = TPTPExca[xi+1]
		if TPTPn < 0 {
			goto ret0
		}
	}
	if TPTPn == 0 {
		/* error ... attempt to resume parsing */
		switch Errflag {
		case 0: /* brand new error */
			TPTPlex.Error(TPTPErrorMessage(TPTPstate, TPTPtoken))
			Nerrs++
			if TPTPDebug >= 1 {
				__yyfmt__.Printf("%s", TPTPStatname(TPTPstate))
				__yyfmt__.Printf(" saw %s\n", TPTPTokname(TPTPtoken))
			}
			fallthrough

		case 1, 2: /* incompletely recovered error ... try again */
			Errflag = 3

			/* find a state where "error" is a legal shift action */
			for TPTPp >= 0 {
				TPTPn = TPTPPact[TPTPS[TPTPp].yys] + TPTPErrCode
				if TPTPn >= 0 && TPTPn < TPTPLast {
					TPTPstate = TPTPAct[TPTPn] /* simulate a shift of "error" */
					if TPTPChk[TPTPstate] == TPTPErrCode {
						goto TPTPstack
					}
				}

				/* the current p has no shift on "error", pop stack */
				if TPTPDebug >= 2 {
					__yyfmt__.Printf("error recovery pops state %d\n", TPTPS[TPTPp].yys)
				}
				TPTPp--
			}
			/* there is no state on the stack with an error shift ... abort */
			goto ret1

		case 3: /* no shift yet; clobber input char */
			if TPTPDebug >= 2 {
				__yyfmt__.Printf("error recovery discards %s\n", TPTPTokname(TPTPtoken))
			}
			if TPTPtoken == TPTPEofCode {
				goto ret1
			}
			TPTPrcvr.char = -1
			TPTPtoken = -1
			goto TPTPnewstate /* try again in the same state */
		}
	}

	/* reduction by production TPTPn */
	if TPTPDebug >= 2 {
		__yyfmt__.Printf("reduce %v in:\n\t%v\n", TPTPn, TPTPStatname(TPTPstate))
	}

	TPTPnt := TPTPn
	TPTPpt := TPTPp
	_ = TPTPpt // guard against "declared and not used"

	TPTPp -= TPTPR2[TPTPn]
	// TPTPp is now the index of $0. Perform the default action. Iff the
	// reduced production is ε, $1 is possibly out of range.
	if TPTPp+1 >= len(TPTPS) {
		nyys := make([]TPTPSymType, len(TPTPS)*2)
		copy(nyys, TPTPS)
		TPTPS = nyys
	}
	TPTPVAL = TPTPS[TPTPp+1]

	/* consult goto table to find next state */
	TPTPn = TPTPR1[TPTPn]
	TPTPg := TPTPPgo[TPTPn]
	TPTPj := TPTPg + TPTPS[TPTPp].yys + 1

	if TPTPj >= TPTPLast {
		TPTPstate = TPTPAct[TPTPg]
	} else {
		TPTPstate = TPTPAct[TPTPj]
		if TPTPChk[TPTPstate] != -TPTPn {
			TPTPstate = TPTPAct[TPTPg]
		}
	}
	// dummy call; replaced with literal code
	switch TPTPnt {

	case 1:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			res = TPTPDollar[1].lstm
		}
	case 2:
		TPTPDollar = TPTPS[TPTPpt-0 : TPTPpt+1]
		{
			TPTPVAL.lstm = nil
		}
	case 3:
		TPTPDollar = TPTPS[TPTPpt-2 : TPTPpt+1]
		{
			TPTPVAL.lstm = append([]basictypes.Statement{TPTPDollar[1].stm}, TPTPDollar[2].lstm...)
		}
	case 4:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.stm = TPTPDollar[1].stm
		}
	case 5:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.stm = TPTPDollar[1].stm
		}
	case 6:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.stm = TPTPDollar[1].stm
		}
	case 7:
		TPTPDollar = TPTPS[TPTPpt-10 : TPTPpt+1]
		{
			TPTPVAL.stm = basictypes.MakeStatement(TPTPDollar[3].val, TPTPDollar[5].fr, TPTPDollar[7].form)
		}
	case 8:
		TPTPDollar = TPTPS[TPTPpt-0 : TPTPpt+1]
		{
		}
	case 10:
		TPTPDollar = TPTPS[TPTPpt-5 : TPTPpt+1]
		{
			TPTPVAL.stm = basictypes.MakeStatement(TPTPDollar[3].val, basictypes.Include, nil)
		}
	case 11:
		TPTPDollar = TPTPS[TPTPpt-9 : TPTPpt+1]
		{
			TPTPVAL.stm = basictypes.MakeStatement(TPTPDollar[3].val, basictypes.Include, nil)
		}
	case 12:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 13:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.ls = []string{TPTPDollar[1].val}
		}
	case 14:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.ls = append([]string{TPTPDollar[1].val}, TPTPDollar[3].ls...)
		}
	case 15:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			switch TPTPDollar[1].val {
			case "axiom":
				TPTPVAL.fr = basictypes.Axiom
			case "conjecture":
				TPTPVAL.fr = basictypes.Conjecture
			}
		}
	case 16:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 17:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 18:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 19:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 20:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 21:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerEqu(TPTPDollar[1].form, TPTPDollar[3].form)
		}
	case 22:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerImp(TPTPDollar[1].form, TPTPDollar[3].form)
		}
	case 23:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerImp(TPTPDollar[3].form, TPTPDollar[1].form)
		}
	case 24:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerOr([]basictypes.Form{basictypes.MakerAnd([]basictypes.Form{TPTPDollar[1].form, basictypes.RefuteForm(TPTPDollar[3].form)}), basictypes.MakerAnd([]basictypes.Form{basictypes.RefuteForm(TPTPDollar[1].form), TPTPDollar[3].form})})
		}
	case 25:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.RefuteForm(basictypes.MakerOr([]basictypes.Form{TPTPDollar[1].form, TPTPDollar[3].form}))
		}
	case 26:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.RefuteForm(basictypes.MakerAnd([]basictypes.Form{TPTPDollar[1].form, TPTPDollar[3].form}))
		}
	case 27:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 28:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 29:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerOr([]basictypes.Form{TPTPDollar[1].form, TPTPDollar[3].form})
		}
	case 30:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerOr([]basictypes.Form{TPTPDollar[1].form, TPTPDollar[3].form})
		}
	case 31:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerAnd([]basictypes.Form{TPTPDollar[1].form, TPTPDollar[3].form})
		}
	case 32:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerAnd([]basictypes.Form{TPTPDollar[1].form, TPTPDollar[3].form})
		}
	case 33:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 34:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 35:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 36:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[2].form
		}
	case 37:
		TPTPDollar = TPTPS[TPTPpt-6 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerAll(TPTPDollar[3].vrl, TPTPDollar[6].form)
		}
	case 38:
		TPTPDollar = TPTPS[TPTPpt-6 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerEx(TPTPDollar[3].vrl, TPTPDollar[6].form)
		}
	case 39:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.vrl = []basictypes.Var{TPTPDollar[1].vrb}
		}
	case 40:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.vrl = append([]basictypes.Var{TPTPDollar[1].vrb}, TPTPDollar[3].vrl...)
		}
	case 41:
		TPTPDollar = TPTPS[TPTPpt-2 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.RefuteForm(TPTPDollar[2].form)
		}
	case 42:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 43:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerPred(basictypes.Id_neq, []basictypes.Term{TPTPDollar[1].term, TPTPDollar[3].term})
		}
	case 44:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 45:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 46:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerPred(TPTPDollar[1].app.symb, TPTPDollar[1].app.args)
		}
	case 47:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.form = TPTPDollar[1].form
		}
	case 48:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			if TPTPDollar[1].val == "true" {
				TPTPVAL.form = basictypes.Top{}
			} else if TPTPDollar[1].val == "false" {
				TPTPVAL.form = basictypes.Bot{}
			}
		}
	case 49:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.form = basictypes.MakerPred(basictypes.Id_eq, []basictypes.Term{TPTPDollar[1].term, TPTPDollar[3].term})
		}
	case 50:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.term = TPTPDollar[1].term
		}
	case 51:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.term = TPTPDollar[1].vrb
		}
	case 52:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.term = basictypes.MakerFun(TPTPDollar[1].app.symb, TPTPDollar[1].app.args)
		}
	case 53:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.term = basictypes.MakerFun(TPTPDollar[1].app.symb, TPTPDollar[1].app.args)
		}
	case 54:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.app = App{TPTPDollar[1].id, []basictypes.Term{}}
		}
	case 55:
		TPTPDollar = TPTPS[TPTPpt-4 : TPTPpt+1]
		{
			TPTPVAL.app = App{TPTPDollar[1].id, TPTPDollar[3].ltrm}
		}
	case 56:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.app = App{basictypes.MakerId(TPTPDollar[1].val), []basictypes.Term{}}
		}
	case 57:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.app = App{basictypes.MakerId(TPTPDollar[1].val), []basictypes.Term{}}
		}
	case 58:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.id = TPTPDollar[1].id
		}
	case 59:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.id = TPTPDollar[1].id
		}
	case 60:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.vrb = basictypes.MakerVar(TPTPDollar[1].val)
		}
	case 61:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.ltrm = []basictypes.Term{TPTPDollar[1].term}
		}
	case 62:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.ltrm = append([]basictypes.Term{TPTPDollar[1].term}, TPTPDollar[3].ltrm...)
		}
	case 83:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].id.GetName()
		}
	case 84:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 85:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.id = basictypes.MakerId(TPTPDollar[1].val)
		}
	case 86:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.id = basictypes.MakerId(TPTPDollar[1].val)
		}
	case 87:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 88:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 89:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 90:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 91:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 92:
		TPTPDollar = TPTPS[TPTPpt-2 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val + TPTPDollar[2].val
		}
	case 93:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 94:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = "0"
		}
	case 95:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 98:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 99:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 100:
		TPTPDollar = TPTPS[TPTPpt-2 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val + TPTPDollar[2].val
		}
	case 101:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 102:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 103:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 104:
		TPTPDollar = TPTPS[TPTPpt-2 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val + TPTPDollar[2].val
		}
	case 105:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 106:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 107:
		TPTPDollar = TPTPS[TPTPpt-2 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val + TPTPDollar[2].val
		}
	case 108:
		TPTPDollar = TPTPS[TPTPpt-2 : TPTPpt+1]
		{
			TPTPVAL.val = "." + TPTPDollar[2].val
		}
	case 109:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val + "E" + TPTPDollar[3].val
		}
	case 110:
		TPTPDollar = TPTPS[TPTPpt-3 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val + "E" + TPTPDollar[3].val
		}
	case 111:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 112:
		TPTPDollar = TPTPS[TPTPpt-1 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val
		}
	case 113:
		TPTPDollar = TPTPS[TPTPpt-2 : TPTPpt+1]
		{
			TPTPVAL.val = TPTPDollar[1].val + TPTPDollar[2].val
		}
	}
	goto TPTPstack /* stack new state and value */
}
