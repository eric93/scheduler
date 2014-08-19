import solver
import json

def pretty_print(schedule):
    ret = ""
    for i in range(len(schedule)):
        for k in schedule[i].keys():
            ret += "visit_" + k + "_" + str(i) + "\n"
            for x in schedule[i][k]:
                for y in x:
                    ret += '\t' + y + '\n'

    return ret


def go():
    s = open('grammar.json').read()
    g = json.loads(s)
    print pretty_print(solver.schedule(g))
