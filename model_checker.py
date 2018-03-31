from interface import parse, getpath
from parsing.parser import Parser
from parsing.lexer import Lexer
from input_paths.path import Path 
from parsing.ast import Ast
from parsing.token import Token, TokenType
from collections import defaultdict
import os


file = os.path.join(os.getcwd(), "paths")
file = os.path.join(file, "path8.txt")
path = Path(file)
# A model checker for LTL on regular paths
calls = {TokenType.X : lambda ident, phi : X(ident,phi),
		 TokenType.G : lambda ident, phi : G(ident,phi),
		 TokenType.F : lambda ident, phi : F(ident,phi),
		 TokenType.ATOM : lambda ident, phi : str(phi.value) in [str(x)[2:] for x in get_state(ident).labeling],
		 TokenType.NOT : lambda ident, phi: not f(ident, phi.right)}
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
	X, G, F, ATOM = TokenType.X, TokenType.G, TokenType.F, TokenType.ATOM
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
			pass
		if tt == TokenType.U:
			pass
		pass
	pass
	
def X(ident, phi):
	return evaluate(ident+1, phi)
def G(ident, phi):
	if ident in mp and phi in mp[ident]:
		return True
	val = True
	for x in range(path_size):
		val = (val and evaluate(ident + x, phi))
	return val
def F(ident, phi):
	if ident in mp and phi in mp[ident]:
		return True
	val = True
	for x in range(path_size):
		val = (val or evaluate(ident + x, phi))
	return val
def U(ident, phi):
	pass

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


form = parse('F(wood_right&&F(sheep_right))')
print(evaluate(0,form))
#print(get_state(0).ident)
	
#print(traverse(parse("(a)U(g)")))
#traverse(parse("X(X(X(a)))&&X(a)"))

