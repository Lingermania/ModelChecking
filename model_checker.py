from interface import parse, getpath
from parsing.parser import Parser
from parsing.lexer import Lexer
from input_paths.path import Path 
from parsing.ast import Ast
from parsing.token import Token, TokenType
from collections import defaultdict
import os


file = os.path.join(os.getcwd(), "paths")
file = os.path.join(file, "path0.txt")
path = Path(file)
# A model checker for LTL on regular paths
calls = {TokenType.X : lambda ident, phi : X(ident, phi),
		 TokenType.G : lambda ident, phi : G(ident, phi),
		 TokenType.F : lambda ident, phi : F(ident, phi),
		 TokenType.U : lambda ident, left, right : U(ident, left, right),
		 TokenType.W : lambda ident, left, right : W(ident, left, right),
		 TokenType.ATOM : lambda ident, phi : str(phi.value) in [str(x)[2:] for x in get_state(ident).labeling],
		 TokenType.NOT : lambda ident, phi: not evaluate(ident, phi)}
mp = defaultdict(list)
path_size = path.total

def get_state(ident):
	global path
	i=0
	state = None
	for x in path.next_state():
		state = x
		if i == ident:
			break
		i+=1
	return state

def evaluate(ident, phi):
	# You do not have to use evaluate as it is here;
	# you can implement modelcheck however you like.
	# This is only a hint.
	X, G, F, U, W, ATOM = TokenType.X, TokenType.G, TokenType.F, TokenType.U, TokenType.W, TokenType.ATOM
	#print(phi.oper())
	#print(phi.arity())
	if phi.arity() == 0:
		#atom
		return calls[ATOM](ident, phi)
	if phi.arity() == 1:
		#unary
		tt = phi.oper()
		return calls[tt](ident, phi.right)
	if phi.arity() == 2:
		#binary
		tt = phi.oper()
		if tt == TokenType.AND:
			return evaluate(ident, phi.left) and evaluate(ident, phi.right)
		if tt == TokenType.OR:
			return evaluate(ident, phi.left) or evaluate(ident, phi.right)
		if tt == TokenType.IMPL:
			if not evaluate(ident, phi.left):
				return True
			else:
				return evaluate(ident, phi.right)
		if tt == TokenType.U:
			return calls[U](ident, phi.left, phi.right)
		if tt == TokenType.W:
			return calls[W](ident, phi.left, phi.right)
		pass
	pass
	
def X(ident, phi):
	return evaluate(ident+1, phi)
def G(ident, phi):
	#if ident in mp and phi in mp[ident]:
	#	return True
	val = True
	for x in range(path_size):
		val = (val and evaluate(ident + x, phi))
	return val
def F(ident, phi):
	#if ident in mp and phi in mp[ident]:
	#	return True
	val = False
	for x in range(path_size):
		val = (val or evaluate(ident + x, phi))
	return val
def U(ident, left,right):
	for x in range(path_size):
		l,r = evaluate(ident + x, left), evaluate(ident + x, right)
		if r: return True
		elif l: continue
		else: return False
	return False
def W(ident, left,right):
	for x in range(path_size):
		l,r = evaluate(ident + x, left), evaluate(ident + x, right)
		if r: return True
		elif l: continue
		else: return False
	return True

def modelcheck(m,f):
	return evaluate(m,f)[0]

def traverse(tree):
	if tree is []:
		return
	print(tree.oper())
	print(tree.arity())
	if tree.children() == []:
		return

	
	if len(tree.children()) == 1:
		right = tree.children()[0]
		traverse(right)
		return

	left, right = tree.children()
	if left is not []:
		traverse(left)
	if right is not []:
		traverse(right)

def rulecheck(rule, num):
	form = parse(rule)
	if evaluate(0, form):
		print(f"Rule {num}: Satisfied")
	else:
		print(f"Rule {num}: Not Satisfied")

first_rule_1 = "!F(wolf_left && goat_left && !employee_left) && !F(wolf_right && goat_right && !employee_right)"
first_rule_2 = "!F(popeye_left && spinach_left && !employee_left) && !F(popeye_right && spinach_right && !employee_right)"
first_rule_3 = "!F(popeye_left && wine_left && computer_left && !employee_left) && !F(popeye_right && wine_right && computer_right  && !employee_right)"
second_rule = "!F((X(X(wolf_left && goat_left && !employee_left)) && X(wolf_left && goat_left && !employee_left) && wolf_left && goat_left && !employee_left) || (X(X(wolf_right && goat_right && !employee_right)) && X(wolf_right && goat_right && !employee_right) && wolf_right && goat_right && !employee_right))"
third_rule = "!F(X(X(X(!employee_trans))) && X(X(!employee_trans)) && X(!employee_trans) && !employee_trans)"
fourth_rule = "(!spinach_right && !popeye_right) U spinach_right"
fifth_rule = "G(goat_trans -> X(!goat_trans W sheep_trans)) && G(sheep_trans -> X(!sheep_trans W goat_trans))"
sixth_rule = "G((employee_left -> X(!employee_right)) && (employee_right -> X(!employee_left)))"

rulecheck(first_rule_1, "1a")
rulecheck(first_rule_2, "1b")
rulecheck(first_rule_3, "1c")
rulecheck(second_rule, "2")
rulecheck(third_rule, "3")
rulecheck(fourth_rule, "4")
rulecheck(fifth_rule, "5")
rulecheck(sixth_rule, "6")
