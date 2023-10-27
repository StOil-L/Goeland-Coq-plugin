/* TODO LIST:
- move to different package
- automatically compile Goeland Coq package when first using the prover
- rewrite rule Delta NotForAll to introduce multiple skolems at once
-- commented text in rule is an unfinished attempt at doing so
-- review getSkolemTransition before use
-- write untranslateSkolems
*/

package main

import (
	"fmt"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"

	proof "github.com/GoelandProver/Goeland/visualization_proof"
)

var (
	coqpackagefolder, coqerr = os.Getwd()
	parameters               CoqParameters
	hypothesisnumber         uint8 = 0
	hypotheses                     = make(map[string]string)
	tobeintroduced                 = make(map[string]string)
	boundvariables                 = make(map[string]string)
	h_order                  []string
	t_order                  []string
	b_order                  []string
	debuginfo                bool = false // Set to true to activate debug terminal prints
)

type CoqParameters struct {
	Predicates []string
	Pred_arity []int
	Functions  []string
	Fun_arity  []int
}

func MakeCoqOutput(goeland_proof []proof.ProofStruct) { // called from main
	if coqerr != nil { // error check on Coq package folder.
		log.Fatal(coqerr)
	}
	coqpackagefolder += "/coq-demo"
	coqoutputname := strings.TrimSuffix(problem_name, filepath.Ext(problem_name))
	_, filerror := os.Stat("coq-demo/goeland.vo")
	if os.IsNotExist(filerror) { // First build / compile of Goéland
		compilecmd := exec.Command("coqc", "-Q", "coq-demo", "Goeland", "coq-demo/goeland.v")
		compilerror := compilecmd.Run()
		if compilerror != nil {
			log.Fatal(compilerror)
		}
	}
	f, err := os.OpenFile("coq-demo/output/"+coqoutputname+".v", os.O_RDWR|os.O_CREATE|os.O_TRUNC, 0755)
	if err != nil {
		log.Fatal(err)
	}
	defer f.Close()

	fmt.Println("% Coq output start Proof for " + problem_name)

	if debuginfo {
		fmt.Println("Proof starts on: " + goeland_proof[0].Formula.ToString())
	}

	f.WriteString("(* PROOF FOUND *)\n")
	writeContext(goeland_proof, f)

	coqformula := makeCoqFormula(goeland_proof[0])
	f.WriteString("(* PROOF BEGIN *)\nTheorem " + coqoutputname + " : " + coqformula + ".\n")

	if specificProblemCheck(goeland_proof[0]) {
		f.WriteString("Proof.\napply NNPP.\n")
	} else {
		f.WriteString("Proof.\napply NNPP. intro " + createHypothesis(coqformula) + ".\n")
		writeRules(goeland_proof, f)
	}

	f.WriteString("Qed.\n(* PROOF END *)")

	hypothesisnumber = 0

	if debuginfo {
		fmt.Println(hypotheses)
	}

	fmt.Println("% Coq output for " + problem_name + " written at " + coqpackagefolder + "/" + coqoutputname + ".v")

}

func writeContext(currentproof []proof.ProofStruct, coqfile *os.File) {
	coqfile.WriteString("(* CONTEXT BEGIN *)\nAdd LoadPath \"" + coqpackagefolder + "\" as Goeland.\n")
	coqfile.WriteString("Require Import Goeland.goeland.\nParameter goeland_U : Set.\n")
	coqfile.WriteString("Parameter goeland_E : goeland_U.\n")
	writeCoqParameters(currentproof[0], coqfile)
	coqfile.WriteString("(* CONTEXT END *)\n")
}

func writeCoqParameters(node proof.ProofStruct, coqfile *os.File) {

	parameters = getCoqParameters(node)

	// Order of defnitions doesn't matter; writing functions then predicates
	for funpos, _ := range parameters.Functions {
		coqfile.WriteString("Parameter " + parameters.Functions[funpos] + " : " + writeParameterArity(parameters.Fun_arity[funpos], false) + ".\n")
	}

	for predpos, _ := range parameters.Predicates {
		coqfile.WriteString("Parameter " + parameters.Predicates[predpos] + " : " + writeParameterArity(parameters.Pred_arity[predpos], true) + ".\n")
	}
}

func getCoqParameters(node proof.ProofStruct) CoqParameters {

	var formulaparameters CoqParameters
	toparse := node.Formula.ToString()
	predregex := regexp.MustCompile(`(((([∀∃] [A-Z]+)|([∨∧⇒⇔])) )|¬)\(*[a-z]+`)
	funregex := regexp.MustCompile(`[a-z]+\(`)
	nameregex := regexp.MustCompile(`[a-z]+`)
	formuladepth := getFormulaDepth(node)

	isPropositional, err := regexp.MatchString(`[∀∃]`, toparse)
	isPropositional = !isPropositional
	if err != nil {
		log.Fatal(err)
	}
	if isPropositional {
		return getOrderZeroParameters(node)
	}

	foundpredicates := predregex.FindAllStringIndex(toparse, -1)
	for _, pred := range foundpredicates {
		currentarity := 1 // Dummy value for getArityFromString to work properly
		currentpred := toparse[pred[0]:pred[1]]
		predname := nameregex.FindStringIndex(currentpred)
		currentpred = currentpred[predname[0]:predname[1]]

		if debuginfo {
			fmt.Println("Current predicate: " + currentpred)
		}

		previouslyadded := false
		for _, addedpred := range formulaparameters.Predicates { // Checks if predicate already exists
			if currentpred == addedpred {
				previouslyadded = true
			}

		}

		if !previouslyadded { // Adds predicate to Predicates, with arity to match
			formulaparameters.Predicates = append(formulaparameters.Predicates, currentpred)
			currentarity = getArityFromString(toparse[pred[1]:], formuladepth[pred[0]])
			formulaparameters.Pred_arity = append(formulaparameters.Pred_arity, currentarity)
		}

	}

	foundfunctions := funregex.FindAllStringIndex(toparse, -1)
	for _, fun := range foundfunctions {
		currentarity := 1 // Dummy value for getArityFromString to work properly
		currentfun := toparse[fun[0]:fun[1]]
		funname := nameregex.FindStringIndex(currentfun)
		currentfun = currentfun[funname[0]:funname[1]]

		if debuginfo {
			fmt.Println("Current function: " + currentfun)
		}

		previouslyadded := false
		for _, addedfun := range formulaparameters.Functions { // Checks if function already exists
			if currentfun == addedfun {
				previouslyadded = true
			}

		}

		isapredicate := false
		for _, addedpred := range formulaparameters.Predicates { // Checks if name doesn't match predicate
			if currentfun == addedpred {
				isapredicate = true
			}

		}

		if !previouslyadded && !isapredicate { // Adds function to Functions, with arity to match
			formulaparameters.Functions = append(formulaparameters.Functions, currentfun)
			currentarity = getArityFromString(toparse[fun[1]-1:], formuladepth[fun[0]])
			formulaparameters.Fun_arity = append(formulaparameters.Fun_arity, currentarity)
		}

	}

	if debuginfo {
		fmt.Println("Predicates collected:", formulaparameters.Predicates)
		fmt.Println("Predicate arities collected:", formulaparameters.Pred_arity)
		fmt.Println("Functions collected:", formulaparameters.Functions)
		fmt.Println("Function arities collected:", formulaparameters.Fun_arity)
	}

	return formulaparameters

}

func getOrderZeroParameters(node proof.ProofStruct) CoqParameters {

	var formulaparameters CoqParameters
	toparse := strings.ToLower(node.Formula.ToString())
	propregex := regexp.MustCompile(`[a-z]+`)

	foundprops := propregex.FindAllStringIndex(toparse, -1)
	for _, prop := range foundprops {
		currentprop := toparse[prop[0]:prop[1]]
		previouslyadded := false

		for _, addedprop := range formulaparameters.Predicates {
			if currentprop == addedprop {
				previouslyadded = true
			}

		}

		if !previouslyadded {
			formulaparameters.Predicates = append(formulaparameters.Predicates, currentprop)
			formulaparameters.Pred_arity = append(formulaparameters.Pred_arity, 0)
		}

	}

	return formulaparameters

}

func makeCoqFormula(node proof.ProofStruct) string { // Turns a Formula into a Coq-compatible formula.

	toconvert := deleteCommas(rearrangeParentheses2(rearrangeParentheses(node.Formula.ToString())))

	if node.Node_id == 0 { // Gets the original formula, not its opposite
		coqstartingchar := 3
		if toconvert[2] != '(' {
			coqstartingchar = 2
		}

		toconvert = toconvert[coqstartingchar : len(toconvert)+(2-coqstartingchar)]
	}

	toconvert = correctParentheses(toconvert)

	convertedformula := ""
	for _, char := range toconvert {
		convertedformula += convertOrderZeroSyntax(char)
	}

	resultformula := convertFirstOrderSyntax(convertedformula)
	if len(b_order) > 0 { // Translates skolems if there are any
		resultformula = translateSkolem(convertFirstOrderSyntax(convertedformula))
	}

	if debuginfo {
		fmt.Println("Current Coq-compatible formula: " + resultformula)
	}

	return resultformula

}

func rearrangeParentheses(stringform string) string { // Moves parentheses for quantifiers and adds additional quantifiers to multiple arity quantifiers

	finalstring := stringform
	quantifierregex := regexp.MustCompile(`(∀|∃) ([A-Z]+(, )?)+ \(`)

	if quantifierregex.MatchString(finalstring) {
		currentquantifier := quantifierregex.FindStringIndex(finalstring)
		terms := finalstring[currentquantifier[0]+4 : currentquantifier[1]-2]
		var split []string
		beginningofstring := finalstring[:currentquantifier[0]]
		restofstring := finalstring[currentquantifier[1]:]
		firstquantifier := finalstring[currentquantifier[0] : currentquantifier[0]+3]

		if strings.Contains(terms, ", ") {
			split = strings.Split(terms, ", ")
			for fpos, f := range split {
				if fpos == len(split)-1 {
					beginningofstring += "(" + firstquantifier + " " + f + " "
				} else {
					beginningofstring += "(" + firstquantifier + " " + f + ", "
				}

			}

		} else {
			beginningofstring += "(" + firstquantifier + " " + terms + " "
		}

		finalstring = beginningofstring + rearrangeParentheses(restofstring)

	}

	return finalstring

}

func rearrangeParentheses2(stringform string) string { // Rearranges parentheses for predicates and terms

	finalstring := stringform
	predtermregex := regexp.MustCompile(`[a-z]+\(`)

	if predtermregex.MatchString(finalstring) {
		currentpredfun := predtermregex.FindStringIndex(finalstring)
		finalstring = finalstring[:currentpredfun[0]] + "(" + finalstring[currentpredfun[0]:currentpredfun[1]-1] + " " + rearrangeParentheses2(finalstring[currentpredfun[1]:])
	}

	return finalstring

}

func deleteCommas(stringform string) string { // Deletes commas that don't directly follow a quantifier
	toparse := strings.Replace(stringform, ",", "", -1)
	quantifierregex := regexp.MustCompile(`(forall|exists) [A-Z]+ : goeland\_U[^,]`)
	if quantifierregex.MatchString(toparse) {
		currentquantifier := quantifierregex.FindStringIndex(toparse)
		currentquantifier[1]--
		toparse = toparse[:currentquantifier[1]] + ", " + deleteCommas(toparse[currentquantifier[1]+1:])
	}
	return toparse
}

func correctParentheses(stringform string) string { // Fixes potential parenthesis mismatches

	openingparenthesisregex := regexp.MustCompile(`\(`)
	closingparenthesisregex := regexp.MustCompile(`\)`)
	openingparenthesescount := len(openingparenthesisregex.FindAllStringIndex(stringform, -1))
	closingparenthesescount := len(closingparenthesisregex.FindAllStringIndex(stringform, -1))

	if openingparenthesescount > closingparenthesescount { // Not enough closing parentheses
		for i := 0; i < (openingparenthesescount - closingparenthesescount); i++ {
			stringform += ")"
		}

	} else if closingparenthesescount < openingparenthesescount { // Not enough opening parentheses
		for i := 0; i < (closingparenthesescount - openingparenthesescount); i++ {
			stringform = "(" + stringform
		}

	}

	return stringform

}

func specificProblemCheck(node proof.ProofStruct) bool { // ONLY USEFUL ON ORDER ZERO PROBLEMS.

	// For some reason, problem ~~a -> a only needs apply NNPP. to complete the proof.
	// The Coq output feature of Zenon, which serves as a basis for Goéland's Coq output feature, overlooks this issue.
	// This function aims to fix this very specific scenario.

	coqformula := makeCoqFormula(node)

	isPropositional, err := regexp.MatchString(`[∀∃]`, strings.ToLower(node.Formula.ToString()))
	isPropositional = !isPropositional
	if err != nil {
		log.Fatal(err)
	}

	if debuginfo {
		fmt.Println("Parameter string length:", len(parameters.Predicates))
		fmt.Println("Coq problem looks like this: " + coqformula + "...")
	}

	if len(parameters.Predicates) == 1 && coqformula == "~~"+parameters.Predicates[0]+" -> "+parameters.Predicates[0] && isPropositional {
		return true
	}

	return false

}

func convertOrderZeroSyntax(char rune) string { // Converts operators into a Coq-compatible form

	toconvert := string(char)
	switch toconvert {
	case "¬":
		return "~"
	case "∧":
		return "/\\"
	case "∨":
		return "\\/"
	case "⇒":
		return "->"
	case "⇔":
		return "<->"
	default:
		return toconvert
	}

}

func convertFirstOrderSyntax(stringform string) string { // Converts quantifiers into a Coq-compatible form

	finalstring := stringform
	forallregexp := regexp.MustCompile(`∀ [A-Z]+`)
	existsregexp := regexp.MustCompile(`∃ [A-Z]+`)
	var forallmatchindex [][]int
	var existsmatchindex [][]int

	if forallregexp.FindAllStringIndex(finalstring, -1) != nil {
		forallmatchindex = forallregexp.FindAllStringIndex(finalstring, -1)
		for i := len(forallmatchindex) - 1; i >= 0; i-- {
			finalstring = finalstring[:forallmatchindex[i][0]] + "forall " + finalstring[forallmatchindex[i][0]+4:forallmatchindex[i][1]] + " : goeland_U, " + finalstring[forallmatchindex[i][1]:]
		}

	}

	if existsregexp.FindAllStringIndex(finalstring, -1) != nil {
		existsmatchindex = existsregexp.FindAllStringIndex(finalstring, -1)
		for i := len(existsmatchindex) - 1; i >= 0; i-- {
			finalstring = finalstring[:existsmatchindex[i][0]] + "exists " + finalstring[existsmatchindex[i][0]+4:existsmatchindex[i][1]] + " : goeland_U, " + finalstring[existsmatchindex[i][1]:]
		}

	} // Predicate analysis is done in rearrangeParentheses2 and getCoqParameters

	return strings.Replace(finalstring, "  ", " ", -1)

}

func writeRules(currentproof []proof.ProofStruct, coqfile *os.File) { // Checks every rule in the proof tree

	for _, p := range currentproof {

		if debuginfo {
			for fpos, f := range p.Result_formulas {
				fmt.Println(p.Node_id, fpos, f.ToString())
			}
		}

		writeOneRule(p, coqfile)

		if debuginfo {
			fmt.Println("rule written")
		}

		if len(p.Children) > 0 {
			writeRules(p.Children[1], coqfile)
			writeRules(p.Children[0], coqfile)
		}

	}

}

func writeOneRule(node proof.ProofStruct, coqfile *os.File) { // Specifies behavior for each rule

	switch node.Rule_name {
	case "CLOSURE":
		coqfile.WriteString(generateClosure(node))
	case "ALPHA_NOT_NOT":
		rulehypothesis := parseAlphaResultingFormulas(node)
		coqfile.WriteString("apply " + fetchHypothesis(node) + ". ")
		coqfile.WriteString("goeland_intro " + introduceNow(rulehypothesis[0]) + ".\n")
	case "ALPHA_AND":
		rulehypotheses := parseAlphaResultingFormulas(node)
		coqfile.WriteString("apply (goeland_and_s _ _ " + fetchHypothesis(node) + "). ")
		coqfile.WriteString("goeland_intro " + introduceNow(rulehypotheses[0]) + ". ")
		coqfile.WriteString("goeland_intro " + introduceNow(rulehypotheses[1]) + ".\n")
	case "ALPHA_NOT_OR":
		rulehypotheses := parseAlphaResultingFormulas(node)
		coqfile.WriteString("apply (goeland_notor_s _ _ " + fetchHypothesis(node) + "). ")
		coqfile.WriteString("goeland_intro " + introduceNow(rulehypotheses[0]) + ". ")
		coqfile.WriteString("goeland_intro " + introduceNow(rulehypotheses[1]) + ".\n")
	case "ALPHA_NOT_IMPLY":
		rulehypotheses := parseAlphaResultingFormulas(node)
		coqfile.WriteString("apply (goeland_notimply_s _ _ " + fetchHypothesis(node) + "). ")
		coqfile.WriteString("goeland_intro " + introduceNow(rulehypotheses[0]) + ". ")
		coqfile.WriteString("goeland_intro " + introduceNow(rulehypotheses[1]) + ".\n")
	case "BETA_NOT_AND":
		rulehypotheses := parseBetaResultingFormulas(node)
		coqfile.WriteString("apply (goeland_notand_s _ _ " + fetchHypothesis(node) + "); ")
		coqfile.WriteString("[ goeland_intro " + introduceNow(rulehypotheses[0]) + " | ")
		coqfile.WriteString("goeland_intro " + introduceLater(rulehypotheses[1]) + " ].\n")
	case "BETA_OR":
		rulehypotheses := parseBetaResultingFormulas(node)
		coqfile.WriteString("apply (goeland_or_s _ _ " + fetchHypothesis(node) + "); ")
		coqfile.WriteString("[ goeland_intro " + introduceNow(rulehypotheses[0]) + " | ")
		coqfile.WriteString("goeland_intro " + introduceLater(rulehypotheses[1]) + " ].\n")
	case "BETA_IMPLY":
		rulehypotheses := parseBetaResultingFormulas(node)
		coqfile.WriteString("apply (goeland_imply_s _ _ " + fetchHypothesis(node) + "); ")
		coqfile.WriteString("[ goeland_intro " + introduceNow(rulehypotheses[0]) + " | ")
		coqfile.WriteString("goeland_intro " + introduceLater(rulehypotheses[1]) + " ].\n")
	case "BETA_EQUIV":
		rulehypotheses := parseBetaResultingFormulas(node)
		coqfile.WriteString("apply (goeland_equiv_s _ _ " + fetchHypothesis(node) + "); ")
		coqfile.WriteString("[ goeland_intro " + introduceNow(rulehypotheses[0]) + "; ")
		coqfile.WriteString("goeland_intro " + introduceNow(rulehypotheses[1]) + " | ")
		coqfile.WriteString("goeland_intro " + introduceLater(rulehypotheses[2]) + "; ")
		coqfile.WriteString("goeland_intro " + introduceLater(rulehypotheses[3]) + " ].\n")
	case "BETA_NOT_EQUIV":
		rulehypotheses := parseBetaResultingFormulas(node)
		coqfile.WriteString("apply (goeland_notequiv_s _ _ " + fetchHypothesis(node) + "); ")
		coqfile.WriteString("[ goeland_intro " + introduceNow(rulehypotheses[0]) + "; ")
		coqfile.WriteString("goeland_intro " + introduceNow(rulehypotheses[1]) + " | ")
		coqfile.WriteString("goeland_intro " + introduceLater(rulehypotheses[2]) + "; ")
		coqfile.WriteString("goeland_intro " + introduceLater(rulehypotheses[3]) + " ].\n")
	// FIRST ORDER LOGIC RULES
	case "DELTA_EXISTS":
		rulehypothesis := parseDeltaGammaResultingFormula(node)
		coqfile.WriteString("elim " + fetchHypothesis(node) + ". goeland_intro " + introduceSkolem(node) + ". ")
		coqfile.WriteString("goeland_intro " + introduceNow(rulehypothesis) + ".\n")
	case "DELTA_NOT_FORALL":
		rulehypothesis := parseDeltaGammaResultingFormula(node)
		/* successiveskolems := len(getSkolemTransition(node))
		for i := 0; i < successiveskolems; i++ {
			coqfile.WriteString("apply (goeland_notallex_s "+createFunType(node)+" "+fetchHypothesis(node)+"). ")
			introducedinter := introduceNow(createIntermediateHypothesis(node))
			coqfile.WriteString("goeland_intro "+introducedinter+". idtac.\n")
			coqfile.WriteString("elim "+introducedinter+". goeland_intro "+introduceSkolem(node)+". ")
			if i == successiveskolems-1 {
				coqfile.WriteString("goeland_intro "+introduceNow(rulehypothesis)+".\n")
			} else {
				coqfile.WriteString("goeland_intro "+introduceNow(rulehypothesis)+".\n")
			}
		} */
		coqfile.WriteString("apply (goeland_notallex_s " + createFunType(node) + " " + fetchHypothesis(node) + "). ")
		introducedinter := introduceNow(createIntermediateHypothesis(node))
		coqfile.WriteString("goeland_intro " + introducedinter + ". idtac.\n")
		coqfile.WriteString("elim " + introducedinter + ". goeland_intro " + introduceSkolem(node) + ". ")
		coqfile.WriteString("goeland_intro " + introduceNow(rulehypothesis) + ".\n")
	case "GAMMA_FORALL":
		rulehypothesis := parseDeltaGammaResultingFormula(node)
		coqfile.WriteString(generateGeneralization(node) + " goeland_intro " + introduceNow(rulehypothesis) + ".\n")
	case "GAMMA_NOT_EXISTS":
		rulehypothesis := parseDeltaGammaResultingFormula(node)
		coqfile.WriteString("apply " + fetchHypothesis(node) + ". exists " + fetchNotExistsTerm(node) + ". ")
		coqfile.WriteString("apply NNPP. goeland_intro " + introduceNow(rulehypothesis) + ".\n")
	default: // This state isn't supposed to be reached
		coqfile.WriteString("(* UNDEFINED RULE *)\n")
	}
}

func generateClosure(node proof.ProofStruct) string {

	if debuginfo {
		fmt.Println("Before fetch: ", tobeintroduced)
	}

	hyp1 := fetchHypothesis(node)
	hyp2 := fetchCounterHypothesis(node)

	if debuginfo {
		fmt.Println(hyp1)
		fmt.Println(hyp2)
		fmt.Println("After fetch: ", tobeintroduced)
	}

	var returnedclosure []string
	if hypotheses[hyp1][0] == '~' {
		returnedclosure = append(returnedclosure, hyp1, hyp2)
	} else {
		returnedclosure = append(returnedclosure, hyp2, hyp1)
	}

	return "exact (" + returnedclosure[0] + " " + returnedclosure[1] + ").\n"

}

func fetchHypothesis(node proof.ProofStruct) string {

	tofetch := makeCoqFormula(node)
	return hypothesisGetter(tofetch)

}

func fetchCounterHypothesis(node proof.ProofStruct) string { // Designed for Closure rule only

	tofetch := makeCoqFormula(node)
	if tofetch[0] == '~' {
		tofetch = tofetch[1:]
	} else {
		tofetch = "~" + tofetch
	}

	return hypothesisGetter(tofetch)

}

func hypothesisGetter(coqformula string) string {

	hypothesis := "ERROR"

	for i := 0; i < len(t_order); i++ {

		if tobeintroduced[t_order[i]] == coqformula {
			hypothesis = t_order[i]
		}

	}

	if hypothesis != "ERROR" {
		hypotheses[hypothesis] = tobeintroduced[hypothesis]
		delete(tobeintroduced, hypothesis)
		deleteHypothesis(hypothesis, t_order)
	} else {

		if debuginfo {
			fmt.Println("No hypotheses to be introduced, checking already existing hypotheses")
		}

		for j := 0; j < len(h_order); j++ {

			if hypotheses[h_order[j]] == coqformula {
				hypothesis = h_order[j]
			}

		}

	}

	return hypothesis

}

func deleteHypothesis(hypothesisname string, ordertable []string) []string {

	i := 0
	hypofound := false

	for j := 0; j < len(ordertable); j++ {
		if !hypofound && ordertable[j] == hypothesisname {
			i = j
			hypofound = true
		}

	}

	copy(ordertable[i:], ordertable[i+1:])
	ordertable[len(ordertable)-1] = ""
	ordertable = ordertable[:len(ordertable)-1]

	return ordertable

}

func parseAlphaResultingFormulas(node proof.ProofStruct) []string {

	toparse := strings.Split(node.Result_formulas[0].ToString(), " - ")[1]
	toparse = toparse[1 : len(toparse)-1]
	depth := 0
	var split []string

	if node.Rule_name != "ALPHA_NOT_NOT" {
		for charpos, char := range toparse {
			currentchar := string(char)
			if currentchar == "," && depth == 0 {
				split = append(split, toparse[:charpos], toparse[charpos+2:])
			} else if currentchar == "(" {
				depth++
			} else if currentchar == ")" {
				depth--
			}

		}

		if debuginfo {
			fmt.Println("1:", split[0], "2:", split[1])
		}

		return split

	}

	// Alpha NotNot returns only one hypothesis
	notnot := []string{toparse}
	return notnot
}

func parseBetaResultingFormulas(node proof.ProofStruct) []string {

	toparse := []string{node.Result_formulas[0].ToString(), node.Result_formulas[1].ToString()}
	toparse[0] = toparse[0][1:len(toparse[0])]
	toparse[1] = toparse[1][1:len(toparse[1])]
	var stringslice []string

	for fpos, f := range toparse { // Gets rid of the node IDs
		toparse[fpos] = strings.Split(f, " - ")[1]
	}

	if node.Rule_name == "BETA_EQUIV" || node.Rule_name == "BETA_NOT_EQUIV" { // Beta Equiv and Beta NotEquiv return 4 hypotheses
		for _, f := range toparse {
			depth := 0
			var split []string
			for charpos, char := range f {
				currentchar := string(char)
				if currentchar == "," && depth == 0 {
					split = append(split, f[:charpos], f[charpos+2:])
				} else if currentchar == "(" {
					depth++
				} else if currentchar == ")" {
					depth--
				}

			}

			stringslice = append(stringslice, split[0][1:], split[1][:len(split[1])-1])
		}

		if debuginfo {
			fmt.Println("1:", stringslice[0], "2:", stringslice[1], "| 1:", stringslice[2], "2:", stringslice[3])
		}

	} else {
		stringslice = append(stringslice, toparse[0][1:len(toparse[0])-1], toparse[1][1:len(toparse[1])-1])

		if debuginfo {
			fmt.Println("1:", stringslice[0], "2:", stringslice[1])
		}

	}

	return stringslice

}

func parseDeltaGammaResultingFormula(node proof.ProofStruct) string {

	toparse := strings.Split(node.Result_formulas[0].ToString(), " - ")[1]
	toparse = toparse[1 : len(toparse)-1]
	return toparse

}

func createHypothesis(stringform string) string {

	hypothesis := "goeland_G"
	if hypothesisnumber != 0 {
		digit := string(int(hypothesisnumber) + '0')
		if hypothesisnumber < 10 {
			// Statement exists to ignore digits 1 to 9
		} else if hypothesisnumber >= 10 && hypothesisnumber < 36 {
			digit = string(int('A' + hypothesisnumber - 10))
		} else {
			digit = string(int('a' + hypothesisnumber - 36))
		}

		hypothesis = "goeland_H" + digit

	}

	hypotheses[hypothesis] = makeCoqFormulaFromString(stringform)
	h_order = append(h_order, hypothesis)
	hypothesisnumber++

	if debuginfo {
		fmt.Println("Current hypothesis introduced as: " + hypothesis)
	}

	return hypothesis

}

func makeCoqFormulaFromString(stringform string) string { // Makes a Coq formula from a string. Unfit for root of proof tree.

	toconvert := correctParentheses(deleteCommas(rearrangeParentheses2(rearrangeParentheses(stringform))))
	convertedformula := ""
	for _, char := range toconvert {
		convertedformula += convertOrderZeroSyntax(char)
	}

	resultformula := convertFirstOrderSyntax(convertedformula)
	if len(b_order) > 0 {
		resultformula = translateSkolem(convertFirstOrderSyntax(convertedformula))
	}

	if debuginfo {
		fmt.Println("Current Coq-compatible formula: " + resultformula)
	}

	return resultformula

}

func introduceLater(stringform string) string {

	tointroduce := createHypothesis(stringform)

	if debuginfo {
		fmt.Println("Later introducing: " + tointroduce)
	}

	tobeintroduced[tointroduce] = hypotheses[tointroduce]
	t_order = append(t_order, tointroduce)

	delete(hypotheses, tointroduce)
	deleteHypothesis(tointroduce, h_order)

	return tointroduce

}

func introduceNow(stringform string) string {

	tointroduce := createHypothesis(stringform)

	if debuginfo {
		fmt.Println("Now introducing: " + tointroduce)
	}

	keyofintro := ""
	matched := false
	for k, v := range tobeintroduced {
		if v == hypotheses[tointroduce] {
			keyofintro = k
			matched = true
		}

	}

	if !matched {
		return tointroduce
	}

	hypotheses[keyofintro] = hypotheses[tointroduce]
	h_order = append(h_order, keyofintro)

	delete(tobeintroduced, keyofintro)
	deleteHypothesis(tointroduce, t_order)

	delete(hypotheses, tointroduce)
	deleteHypothesis(tointroduce, h_order)

	hypothesisnumber--

	return keyofintro

}

/* ///////////////////////////////////////////////////////
THE FOLLOWING FUNCTIONS ARE EXCLUSIVE TO FIRST ORDER LOGIC
/////////////////////////////////////////////////////// */

func getFormulaDepth(node proof.ProofStruct) []int { // Returns an array of depth per character in Formula

	formula := node.Formula.ToString()
	var deptharray []int
	depth := 0

	for _, char := range formula {
		currentchar := string(char)
		switch currentchar {
		case "(":
			depth++
		case ")":
			depth--
		default:
		}

		deptharray = append(deptharray, depth)
	}

	return deptharray

}

func getArityFromString(stringform string, desireddepth int) int {

	arity := 1
	functiondepth := desireddepth

	for _, char := range stringform {
		if string(char) == "(" {
			functiondepth++
		}

		if string(char) == ")" {
			if functiondepth == desireddepth {
				return arity
			} else {
				functiondepth--
			}
		}

		if string(char) == "," && functiondepth == desireddepth+1 {
			arity++
		}

	}

	return arity

}

func writeParameterArity(arity int, isPredicate bool) string {

	coqarity := ""

	for i := 0; i < arity; i++ {
		coqarity += "goeland_U -> "
	}

	if isPredicate {
		return coqarity + "Prop"
	}

	return coqarity + "goeland_U"

}

func generateGeneralization(node proof.ProofStruct) string { // Generates a generalization for rule Gamma ForAll

	togeneralize := fetchHypothesis(node)
	generalizer := "goeland_E"

	if len(b_order) > 0 {

		coqforallregex := regexp.MustCompile(`forall [A-Z]+`)

		if coqforallregex.MatchString(togeneralize) { // Looks into boundvariables for match
			currentquantifier := coqforallregex.FindStringIndex(togeneralize)
			deducedterm := togeneralize[currentquantifier[0]+7 : currentquantifier[1]]
			matchfound := false

			for i := 0; i < len(b_order); i++ {

				if strings.Contains(boundvariables[b_order[i]], deducedterm) && !matchfound {
					generalizer = boundvariables[b_order[i]]
					matchfound = true
				}

			}

		} else { // Defaults to first bound variable ever introduced
			generalizer = boundvariables[b_order[0]]
		}
	} else { // Adds default generalizer to boundvariables
		boundvariables["GENERALIZER"] = generalizer
		b_order = append(b_order, "GENERALIZER")
	}

	return "generalize (" + togeneralize + " " + generalizer + ")."

}

func introduceSkolem(node proof.ProofStruct) string {

	toparse := makeCoqFormulaFromString(parseDeltaGammaResultingFormula(node))
	skolemregex := regexp.MustCompile(`skolem_[A-Z]+[0-9]+`)
	newskolemfound := false
	skolemhypothesis := "goeland_T"

	if skolemregex.MatchString(toparse) {
		for !newskolemfound {

			currentskolem := skolemregex.FindStringIndex(toparse)
			skolemname := toparse[currentskolem[0]:currentskolem[1]]
			matchfound := false

			for i := 0; i < len(b_order); i++ {

				if b_order[i] == skolemname {
					matchfound = true
				}

			}

			if !matchfound { // Creates the hypothesis and adds it to boundvariables
				funtypebase := createFunType(node)
				funtyperegex := regexp.MustCompile(`fun [A-Z]+`)
				funtypepos := funtyperegex.FindStringIndex(funtypebase)
				skolemhypothesis += funtypebase[funtypepos[0]+4 : funtypepos[1]]
				boundvariables[skolemname] = skolemhypothesis
				b_order = append(b_order, skolemname)
				newskolemfound = true
			} else {
				return boundvariables[skolemname]
			}

		}

	} else { // Fetches a Coq counterpart of a skolem
		introducedskolemregex := regexp.MustCompile(`goeland_T[A-Z]+`)
		if introducedskolemregex.MatchString(toparse) {
			foundskolem := introducedskolemregex.FindStringIndex(toparse)
			return toparse[foundskolem[0]:foundskolem[1]]
		}

	}

	return skolemhypothesis

}

func translateSkolem(stringform string) string { // Replaces skolems in formula with their Coq counterpart

	toparse := stringform
	skolemregex := regexp.MustCompile(`skolem_[A-Z]+[0-9]+`)
	fullyparsed := false

	for !fullyparsed {

		if skolemregex.MatchString(toparse) {
			currentskolem := skolemregex.FindStringIndex(toparse)
			skolemname := toparse[currentskolem[0]:currentskolem[1]]
			matchfound := false

			for i := 0; i < len(b_order); i++ {

				if b_order[i] == skolemname && !matchfound {
					toparse = toparse[:currentskolem[0]] + boundvariables[skolemname] + toparse[currentskolem[1]:]
					matchfound = true
				}

			}

			if !matchfound {
				return toparse
			}

		} else {
			fullyparsed = true
		}

	}

	if debuginfo {
		fmt.Println("Formula with skolems translated: " + toparse)
	}

	return toparse

}

func createFunType(node proof.ProofStruct) string { // Creates a temporary function used in rule Delta NotForAll

	toconvert := makeCoqFormula(node)[1:]
	if string(makeCoqFormula(node)[0]) != "(" { // Prevents parenthesis mismatch
		toconvert = makeCoqFormula(node)
	}

	coqforallregex := regexp.MustCompile(`forall [A-Z]+ : goeland_U,`)

	if debuginfo {
		fmt.Println("Delta NotForAll formula: " + toconvert)
	}

	if coqforallregex.MatchString(toconvert) {
		coqforall := coqforallregex.FindStringIndex(toconvert)

		if debuginfo {
			fmt.Println("fun type based on: " + toconvert[coqforall[0]+6:coqforall[1]-1])
		}

		// If lacking parentheses for proper fun type syntax, adds them
		openingparenthesis := ""
		if toconvert[:coqforall[0]] == "" {
			openingparenthesis = "("
		}
		closingparenthesis := ")"
		if openingparenthesis == "(" {
			closingparenthesis = ")"
		}

		toconvert = openingparenthesis + toconvert[:coqforall[0]] + "fun" + toconvert[coqforall[0]+6:coqforall[1]-1] + " =>" + toconvert[coqforall[1]:] + closingparenthesis

	}

	if string(toconvert[0]) == "~" {
		toconvert = toconvert[1 : len(toconvert)-1]
	}

	return toconvert

}

func fetchNotExistsTerm(node proof.ProofStruct) string { // Used to fetch any combination of functions

	currentformula := makeCoqFormula(node)
	resultformula := makeCoqFormulaFromString(parseDeltaGammaResultingFormula(node))
	coqexistsregex := regexp.MustCompile(`exists [A-Z]+ : goeland_U, \(`)
	tofetch := "ERROR"

	if coqexistsregex.MatchString(currentformula) {
		currentquantifier := coqexistsregex.FindStringIndex(currentformula)
		tofetch = currentformula[currentquantifier[0]+7 : currentquantifier[1]-15]
		currentformula = currentformula[:currentquantifier[0]] + currentformula[currentquantifier[1]:len(currentformula)-1]

		if debuginfo {
			fmt.Println("NotExists term to fetch: " + tofetch)
			fmt.Println("Current formula after transformation: " + currentformula)
		}

		termbegin := strings.Index(currentformula, tofetch)
		depth := 0
		substitutefound := false
		termend := termbegin

		for i := termbegin; i < len(resultformula); i++ {
			if !substitutefound {
				currentchar := string(resultformula[i])
				if (currentchar == " " || currentchar == ")") && depth <= 0 {
					termend = i
					substitutefound = true
				} else if currentchar == ")" {
					depth--
				} else if currentchar == "(" {
					depth++
				}

			}

		}

		if tofetch == resultformula[termbegin:termend] {
			return "goeland_E"
		}
		tofetch = resultformula[termbegin:termend]

		if debuginfo {
			fmt.Println("Fetched NotExists term: " + tofetch)
		}

	}

	return tofetch
}

func createIntermediateHypothesis(node proof.ProofStruct) string { // Creates an hypothesis to eliminate within rule DeltaNotForAll

	toconvert := makeCoqFormula(node)
	intermedhypregex := regexp.MustCompile(`~\(forall [A-Z]+ : goeland_U, `)
	doubleparenthesesregex := regexp.MustCompile(`\(\(+`)

	if intermedhypregex.MatchString(toconvert) {
		currentintermedhyp := intermedhypregex.FindStringIndex(toconvert)
		term := toconvert[currentintermedhyp[0]+9 : currentintermedhyp[1]-14]
		properparenthesing := "~(" + toconvert[currentintermedhyp[1]:]

		if doubleparenthesesregex.MatchString(toconvert[currentintermedhyp[1]:]) {
			properparenthesing = "~" + toconvert[currentintermedhyp[1]:len(toconvert)-1]
		}

		toconvert = "exists " + term + " : goeland_U, " + properparenthesing
		toconvert = strings.Replace(toconvert, term, strings.ToLower(term), -1)
	}

	return toconvert

}

func getSkolemTransition(node proof.ProofStruct) []string { // Returns the skolems introduced during rule Delta NotForAll. Currently unused.

	beginformula := node.Formula.ToString()
	endformula := parseDeltaGammaResultingFormula(node)
	skolemregex := regexp.MustCompile(`skolem_[A-Z]+[0-9]+`)
	var beginskolems []string
	var endskolems []string

	if skolemregex.MatchString(beginformula) { // Gets all skolems from beginning of rule
		foundskolems := skolemregex.FindAllStringIndex(beginformula, -1)
		for _, skolem := range foundskolems {
			matchfound := false
			for _, addedskolem := range beginskolems {
				if beginformula[skolem[0]:skolem[1]] == addedskolem {
					matchfound = true
				}

			}

			if !matchfound {
				beginskolems = append(beginskolems, beginformula[skolem[0]:skolem[1]])
			}

		}

	}

	if skolemregex.MatchString(endformula) { // Gets all skolems from end of rule
		foundskolems := skolemregex.FindAllStringIndex(endformula, -1)
		for _, skolem := range foundskolems {
			matchfound := false
			for _, addedskolem := range endskolems {
				if endformula[skolem[0]:skolem[1]] == addedskolem {
					matchfound = true
				}

			}

			if !matchfound {
				endskolems = append(endskolems, endformula[skolem[0]:skolem[1]])
			}

		}

	}
	// Introducing a temporary transition to substract skolems from the final transition
	tempskolemtransition := endskolems
	for _, beginskolem := range beginskolems {
		for endskolempos, endskolem := range endskolems {
			if beginskolem == endskolem {
				tempskolemtransition[endskolempos] = "ALREADYKNOWN"
			}

		}

	}

	var finalskolemtransition []string
	for _, skolem := range tempskolemtransition {
		if skolem != "ALREADYKNOWN" {
			finalskolemtransition = append(finalskolemtransition, skolem)
		}

	}

	return finalskolemtransition

}

// untranslateSkolems: replaces any occurences with their skolem counterparts. Not written.
