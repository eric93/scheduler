import solver
import json

s = open('grammar.json').read()
g = json.loads(s)
solver.schedule(g)
