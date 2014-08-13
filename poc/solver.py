#!/bin/env python2
from z3 import *

num = 0
def genSym():
    global num
    num += 1
    return 'x-' + str(num)

def getSolver(nodes, edges):
    s = z3.Solver()

    for node_num in nodes:
        n = Int('n' + str(node_num))
        s.add(n == node_num)

    dependency = Function('depends-on',IntSort(),IntSort(),BoolSort());
    for e in edges:
        s.add(dependency(e[1],e[0]))

    # (a depends on b) and (b depends on c) => a depends on c
    a = Int(genSym())
    b = Int(genSym())
    c = Int(genSym())
    s.add(ForAll([a,b,c], Implies(And(dependency(a,b),dependency(b,c)),dependency(a,c))))

    result = Function('partition', IntSort(),IntSort())
    h = Int(genSym())
    s.add(ForAll([h], 1 <= result(h)))

    d = Int(genSym())
    e = Int(genSym())

    s.add(ForAll([d,e],\
            Implies(dependency(d,e), result(d) >= result(e))))

    return (s,result,len(nodes))

def getSolution(solver):
    (s, f, num_nodes) = solver
    (model, num_partitions) = findMinimal(s,f,num_nodes)

    traversals = []
    for i in range(num_partitions):
        traversals.append(set())

    for i in range(1, num_nodes + 1):
        cur_trav = model.evaluate(f(i)).as_long()
        traversals[cur_trav - 1].add(i)

    return traversals

def addConstraint(solver, sets):
    (sol, f, n) = solver
    for s in sets:
        l = list(s)
        prev = None
        prevNode = None
        for node in l:
            if prev == None:
                prev = f(IntVal(l[0])) == f(IntVal(l[-1]))
            else:
                prev = And(prev, f(IntVal(node)) == f(IntVal(prevNode)))
            prevNode = node

        sol.add(Not(prev))


def findMinimal(solver,mapping,domain):
    ret = None
    maxVal = 0
    solver.push()
    while True:
        if(solver.check() == sat):
            ret = solver.model()
            maxVal = 0
            for i in range(1,domain + 1):
                maxVal=max(maxVal, ret.evaluate(mapping(i)).as_long())

            print 'Found solution with at most ' + str(maxVal) + ' traversals, iterating...'

            qv = Int(genSym())
            solver.add(ForAll([qv], mapping(qv) < maxVal))
        else:
            if ret != None:
                print 'Using solution with at most ' + str(maxVal) + ' traversals.'
                solver.pop()
                return (ret, maxVal)
            else:
                raise Exception('Could not find a solution')
