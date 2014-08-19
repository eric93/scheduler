import solver
import json

def go():
    s = open('grammar.json').read()
    g = json.loads(s)
    return solver.schedule(g)
