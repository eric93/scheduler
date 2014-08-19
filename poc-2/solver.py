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
    child, attr = parseAttr(val)
    return asgn_types[(className(cls),child,attr)] == 'inh'

def initialize(g):
    node_num = 0
    for c in classes(g):
        for a in assignments(c):
            (child, attr) = parseAttr(a)

            nodes[(className(c),child,attr)] = z3.IntVal(node_num)
            node_num += 1

            if child == 'self':
                asgn_types[(className(c),child,attr)] = 'syn'
                for parent_c in classes(g):
                    for ch in children(parent_c):
                        if className(c) in childClasses(ch):
                            asgn_types[(className(parent_c),childName(ch),attr)] = 'syn'
            else:
                asgn_types[(className(c),child,attr)] = 'inh'
                for ch in children(c):
                    for cc in childClasses(ch):
                        asgn_types[(cc,'self',attr)] = 'inh'

def mayWrite(asgn, cls, grammar):
    (child, attr) = parseAttr(asgn)
    if child == 'self' and asgn_types[(className(cls),child,attr)] == 'syn':
        return [(className(cls),child,attr,'self')]
    if child != 'self' and asgn_types[(className(cls),child,attr)] == 'inh':
        return [(className(cls),child,attr,'self')]

    ret = []
    if child == 'self' and asgn_types[(className(cls),child,attr)] == 'inh':
        for c in classes(grammar):
            for ch in children(c):
                if className(cls) in childClasses(ch):
                    ret.append((className(c),childName(ch),attr, childName(ch)))
    elif child != 'self' and asgn_types[(className(cls),child,attr)] == 'syn':
        for ch in children(cls):
            if childName(ch) == child:
                for cc in childClasses(ch):
                    ret.append((cc,'self',attr, childName(ch)))

    return ret

def mayRead(asgn, cls, grammar):
    (child, attr) = parseAttr(asgn)
    return [(className(cls),child,attr)]

def z3Val(val):
    return nodes[val]

def getInherited(attr,child,cls):
    return asgn_types[(cls,child,attr)] == 'inh'
def getSynthesized(attr,child,cls):
    return asgn_types[(cls,child,attr)] == 'syn'

def schedule(grammar):
    initialize(grammar)
    solver = z3.Solver()
    solver.set(unsat_core=True)

    def nonnegative(x):
        qv = z3.Int(genSym())
        solver.add(z3.ForAll([qv], x(qv) >= 0))

    traversals = z3.Function('trav', z3.IntSort(), z3.IntSort())
    visitors = z3.Function('visit', z3.IntSort(), z3.IntSort())
    nonnegative(traversals)
    nonnegative(visitors)

    childVisits = dict()

    for c in classes(grammar):
        for ch in children(c):
            childVisits[(className(c),childName(ch))] = z3.Function('visit-' + className(c) + '-' + childName(ch), z3.IntSort(), z3.IntSort())
            nonnegative(childVisits[(className(c),childName(ch))])

    for c in classes(grammar):
        for a in assignments(c):
            for d in dependencies(a,c):
                for (dClass,dChild,dAttr,cName) in mayWrite(d,c,grammar):
                    for (aClass,aChild,aAttr) in mayRead(a,c,grammar):
                        start = (dClass,dChild,dAttr)
                        print "start:",start
                        end = (aClass,aChild,aAttr)
                        print "end:",end
                        solver.assert_and_track(traversals(z3Val(start)) <= traversals(z3Val(end)), z3.Bool(dChild +'@'+dClass+'.'+dAttr+' => ' + aChild +'@' + aClass + '.' + aAttr))

                        if getInherited(dAttr,dChild,dClass) and cName != 'self':
                            # trav(a) == trav(d) => visit(d) < visit_child(trav(d))
                            solver.assert_and_track(z3.Implies(traversals(z3Val(start)) == traversals(z3Val(end)),\
                                visitors(z3Val(start)) < childVisits[(dClass, dChild)](traversals(z3Val(start)))),\
                                z3.Bool(dClass + '_visit_' + dChild + ' > ' + dChild +'@'+dClass+'.'+dAttr))
                        elif getSynthesized(dAttr,dChild,dClass) and cName != 'self':
                            # trav(a) == trav(d) =>  visit_child(trav(a)) < visit(a)
                            solver.assert_and_track(z3.Implies(traversals(z3Val(start)) == traversals(z3Val(end)),\
                                 childVisits[(aClass, cName)](traversals(z3Val(end))) < visitors(z3Val(end))),\
                                 z3.Bool(aClass + '_visit_' + aChild + ' < ' + aChild +'@'+aClass+'.'+aAttr))
                        elif aClass == dClass:
                            # trav(a) == trav(d) => visit(a) < visit(d)
                            solver.assert_and_track(z3.Implies(traversals(z3Val(start)) == traversals(z3Val(end)), visitors(z3Val(start)) < visitors(z3Val(end))), z3.Bool(dChild +'@'+dClass+'.'+dAttr+' -> ' + aChild +'@' + aClass + '.' + aAttr))
                        else:
                            raise Exception("Invalid dependency (" + dClass + "," + dChild + "," + dAttr + ") -> (" + aClass + "," + aChild + "," + aAttr + ")")



    if solver.check() == z3.unsat:
        print "Could not find solution."
        print "Unsat core: "
        print solver.unsat_core()
        return

    print solver.model()

    return decode(solver.model(),traversals,visitors,childVisits)

def decode(model, trav, visit, visitors):
    travmax = 0
    for i in range(len(nodes)):
        travcur = model.evaluate(trav(i)).as_long()
        if travcur > travmax:
            travmax = travcur

    traversals = [dict() for i in range(travmax+1)]

    for n in nodes.keys():
        t = model.evaluate(trav(nodes[n])).as_long()
        print 't:',t
        (cls,child,attr) = n
        if not traversals[t].has_key(cls):
            traversals[t][cls] = []

        v = model.evaluate(visit(nodes[n])).as_long()
        if len(traversals[t][cls]) <= v:
            for i in range(len(traversals[t][cls]),v+1):
                traversals[t][cls].append([])

        traversals[t][cls][v].append(child + '.' + attr)

    for vis in visitors.keys():
        for i in range(len(traversals)):
            (cls,child) = vis
            if not traversals[i].has_key(cls):
                traversals[i][cls] = []

            v = model.evaluate(visitors[vis](z3.IntVal(i))).as_long()
            if len(traversals[i][cls]) <= v:
                for j in range(len(traversals[i][cls]),v+1):
                    traversals[i][cls].append([])


            traversals[i][cls][v].append(child + '.visit()')



    return traversals
