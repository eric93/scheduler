#!/usr/bin/env python2

import csv
from solver import getSolver, getSolution, addConstraint
from verifier import verify

def load(filename):
    inp = open(filename)
    reader = csv.reader(inp)

    num_nodes = -1
    num_edges = -1
    cur_node = -1
    cur_edge = -1

    node_names = dict()
    edges = set()

    for row in reader:
        if num_nodes < 0:
            num_nodes = int(row[0])
            cur_node = 1
        elif cur_node <= num_nodes:
            node_names[cur_node] = (row[0], row[1], row[2])
            cur_node += 1
        elif num_edges < 0:
            num_edges = row[0]
            cur_edge = 1
        elif cur_edge <= num_edges:
            edges.add((int(row[0]),int(row[1]),row[2]))
            cur_edge += 1
        else:
            raise Exception("Invalid file format")

    return (node_names, edges)

def main():
    (nodes,edges) = load('input.csv')

    solver = getSolver(nodes, edges)
    while True:
        solution = getSolution(solver)
        (success, output) = verify(solution,nodes,edges)
        if success:
            print "Found schedule: " + str(output)
            return output
        else:
            addConstraint(solver, output)


if __name__ == "__main__":
    main()
