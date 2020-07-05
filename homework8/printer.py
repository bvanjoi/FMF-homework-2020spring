from ast import *


test_stms = [StmAssign('s', ExpNum(0)),
             StmAssign('i', ExpNum(0)),
             StmWhile(ExpBop(ExpVar('i'), ExpBop(ExpVar('n'), ExpNum(3), BOp.MIN), BOp.LE),
                      [StmAssign('s', ExpBop(ExpVar('s'), ExpVar('i'), BOp.ADD)),
                       StmAssign('i', ExpBop(ExpVar('i'), ExpNum(1), BOp.ADD)),
                       StmIf(ExpBop(ExpVar('s'), ExpVar('i'), BOp.GT),
                             [StmAssign("b", ExpBop(ExpVar('s'), ExpNum(1), BOp.MIN))],
                             [])
                       ]),
             StmIf(ExpBop(ExpVar('s'), ExpVar('i'), BOp.GT),
                   [StmAssign("s", ExpBop(ExpVar('i'), ExpNum(1), BOp.MIN))],
                   [StmAssign("s", ExpBop(ExpVar('i'), ExpNum(1), BOp.ADD))])
             ]

test_func = Function(name='printer_test', args=['n'], stms=test_stms, ret=ExpVar('s'))

# your code should print like:
#
# printer_test(n){
#     s = 0;
#     i = 0;
#     while(i <= (n - 3)){
#         s = s + i;
#         i = i + 1;
#         if(s > i){
#             b = s - 1;
#         }
#     }
#     if(s > i){
#         s = i - 1;
#     }
#     else{
#         s = i + 1;
#     }
#     return s;
# }
#
print(test_func)
