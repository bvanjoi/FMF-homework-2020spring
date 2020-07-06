from z3 import *

class Todo(Exception):
    pass

# program equivalence:
# in the class, we present two implementation of the same algorithms, one
# is:
'''
int power3(int in){
  int i, out_a;
  out_a = in;
  for(i = 0; i < 2; i++)
    out_a = out_a * in;
  return out_a;
}
'''
# and the other one is:
'''
int power3_new(int in){
  int out_b;
  out_b = (in*in)*in;
  return out_b;
}

'''
# and with EUF, we can prove that these two algorithm are equivalent,
# that is:
# P1/\P2 -> out_a==out_b

# Please construct, manually, the propositions P1 and P2, and let Z3
# prove the above implication. (Note that you don't need to generate
# P1 or P2 automatically, just write down them manually.)
# TODO: your code here:
# P1 = ...
# P2 = ...
# solve(...)

S = DeclareSort('S')
f = Function('f', S,S, S)
in_ = Const('in_', S)
output_a_0, output_a_1, output_a_2, output_b = Consts('output_a_0 output_a_1 output_a_2 output_b', S)
P1 = And( output_a_0 == in_, output_a_1 == f(output_a_0, in_), output_a_2 == f(output_a_1, in_))
P2 = output_b == f( f(in_,in_), in_)
F = Implies( And(P1,P2), output_a_2 == output_b)
solve(F)