#!/bin/env python2
import z3

nodes = dict()
asgn_types = dict()

num = 0
def genSym():
    global num
    num += 1
    return 'x-' + str(num)

def parseAttr(a):
    return tuple(a.split('.'))
def classes(grammar):
    return grammar.items()
def assignments(cls):
    return cls[1]['asgns'].keys()
def dependencies(asgn,cls):
    return cls[1]['asgns'][asgn]
def getChild(x):
    return parseAttr(x)[0]
def className(cls):
    return cls[0]
def children(cls):
    return cls[1]['children'].items()
def childClasses(child):
    return child[1]
def childName(child):
    return child[0]
def allChildClasses(cls):
    return set(reduce(lambda x,y: x + y, cls[1]['children'].values(), []))
def inherited(val,cls):
    (child, attr) = parseAttr(val)
    return asgn_types[(className(cls),child,attr)] == 'inh'

def initialize(g):
    node_num = 0
    for c in classes(g):
        for a in assignments(c):
            (child, attr) = parseAttr(a)

            nodes[('asgn',className(c),child,attr)] = z3.IntVal(node_num)
            node_num += 1

            if child == 'self':
                asgn_types[(className(c),child,attr)] = 'syn'
                for parent_c in classes(g):
                    for ch in children(parent_c):
                        if c in childClasses(ch):
                            print '(',className(parent_c),',',ch,',',attr,')'
                            asgn_types[(className(parent_c),ch,attr)] = 'syn'
            else:
                asgn_types[(className(c),child,attr)] = 'inh'
                for ch in children(c):
                    for cc in childClasses(ch):
                        asgn_types[(cc,'self',attr)] = 'inh'

def mayWrite(asgn, cls, grammar):
    (child, attr) = parseAttr(asgn)
    if child == 'self' and asgn_types[(className(cls),child,attr)] == 'syn':
        return [nodes[('asgn',className(cls),child,attr)]]
    if child != 'self' and asgn_types[(className(cls),child,attr)] == 'inh':
        return [nodes[('asgn',className(cls),child,attr)]]

    ret = []
    if child == 'self' and asgn_types[(className(cls),child,attr)] == 'inh':
        for c in classes(grammar):
            for ch in children(c):
                if className(cls) in childClasses(ch):
                    ret.append(nodes[('asgn',className(c),childName(ch),attr)])
    elif child != 'self' and asgn_types[(className(cls),child,attr)] == 'syn':
        for ch in allChildClasses(c):
            if childName(ch) == child:
                ret.append(nodes[('asgn',className(ch),'self',attr)])

    return ret

def mayRead(asgn, cls, grammar):
    (child, attr) = parseAttr(asgn)
    return [nodes[('asgn',className(cls),child,attr)]]

def assignsToChild(a):
    (child, attr) = parseAttr(a)
    return child != 'self'

def readsFromChild(a):
    (child, attr) = parseAttr(a)
    return child != 'self'

def selfAssign(a):
    (child, attr) = parseAttr(a)
    return child == 'self'

def getAssign(a,cls):
    (child,attr) = parseAttr(a)
    return nodes[('asgn',className(cls),child,attr)]

def schedule(grammar):
    initialize(grammar)
    solver = z3.Solver()

    def nonnegative(x):
        qv = z3.Int(genSym())
        solver.add(z3.ForAll([qv], x(qv) >= 0))

    traversals = z3.Function('trav', z3.IntSort(), z3.IntSort())
    visitors = z3.Function('visit', z3.IntSort(), z3.IntSort())
    nonnegative(traversals)
    nonnegative(visitors)

    def local_dependence(asgn_to,asgn_from):
        return z3.Implies(traversals(asgn_from) == traversals(asgn_to), visitors(asgn_from) < visitors(asgn_to))
    def visit_incoming(visit, asgn_from):
        return visit(traversals(asgn_from)) > visitors(asgn_from)
    def visit_outgoing(visit, asgn_to):
        return visit(traversals(asgn_to)) < visitors(asgn_to)

    childVisits = dict()
    for c in classes(grammar):
        for ch in children(c):
            childVisits[(className(c),childName(ch))] = z3.Function('visit-' + str(c) + '-' + str(ch), z3.IntSort(), z3.IntSort())
            nonnegative(childVisits[(className(c),childName(ch))])

        for a in assignments(c):
            for d in dependencies(a,c):
                for start in mayWrite(d,c,grammar):
                    for end in mayRead(a,c,grammar):
                        solver.add(traversals(start) <= traversals(end))

                if assignsToChild(a) and readsFromChild(d):
                    solver.add(visit_outgoing(childVisits[(className(c),getChild(d))],getAssign(a,c)))
                    solver.add(visit_incoming(childVisits[(className(c),getChild(a))],getAssign(a,c)))
                elif assignsToChild(a) and selfAssign(d) and not inherited(d,c):
                    solver.add(local_dependence(getAssign(a,c),getAssign(d,c)))
                    solver.add(visit_incoming(childVisits[(className(c),getChild(a))],getAssign(a,c)))
                elif selfAssign(a) and readsFromChild(d):
                    solver.add(visit_outgoing(childVisits[(className(c),getChild(d))],getAssign(a,c)))
                elif selfAssign(a) and selfAssign(d) and not inherited(d,c):
                    solver.add(local_dependence(getAssign(a,c),getAssign(d,c)))

    if solver.check() == z3.unsat:
        print "Could not find solution."
        return

    return (solver.model(),traversals,visitors,childVisits)
