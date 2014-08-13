def verify(traversals,nodes,edges):
    print 'Verifying...'
    cex = []
    output = []
    for t in traversals:
        (success, result) = verifyTraversal(t,nodes,edges)
        if success:
            output.append(result)
        else:
            cex.append(result)

    def prettify(sets):
        ret = ""
        for s in sets:
            ret += str(s) + ","

        return ret

    if len(cex) > 0:
        print "Adding constraints: the following nodes must be on different traversals"
        print prettify(cex)
        return (False, cex)
    else:
        return (True, output)


def verifyTraversal(traversal,nodes,edges):
    class_mapping = dict()
    output = dict()
    cex = []
    for n in nodes.keys():
        class_mapping[nodes[n][0]] = set()

    for node in traversal:
        class_mapping[nodes[node][0]].add(node)

    for c in class_mapping.keys():
        (success,res) = verifyClass(class_mapping[c],edges,nodes)
        if success:
            output[c] = res
        else:
            cex += res

    if len(cex) > 0:
        return (False, cex)
    else:
        return (True, output)

def verifyClass(nodes,edges,node_names):
    def childName(node):
        return node_names[node][1]

    # Some nice data structures to keep everthing linear time
    total_nodes = set()
    unvisited_nodes = set()
    for node in nodes:
        unvisited_nodes.add(node)
        total_nodes.add(node)
        if childName(node) != 'self':
            unvisited_nodes.add(childName(node))
            total_nodes.add(childName(node))

    # Here we store all incoming edges to a given node.
    # We also store all incoming edges to a given child name,
    # to make it easy to add child visitors to the topological sort.
    incoming = dict()
    for n in nodes:
        incoming[n] = set()
        if childName(n) != 'self':
            incoming[childName(n)] = set()
    for e in edges:
        if incoming.has_key(e[1]) and e[2] == 'local':
            incoming[e[1]].add(e)
        elif incoming.has_key(e[1]) and e[2] == 'syn':
            incoming[e[1]].add((childName(e[1]),e[1],'syn'))
        elif incoming.has_key(childName(e[0])) and e[2] == 'inh':
            incoming[childName(e[0])].add(e)


    # Returns true if all nodes can be topologically sorted. result is equal to the sorted order in this case
    # Returns false if there is a cycle in the dependency graph. In this case result is the list of all nodes along the cycle
    def visit(node,edges,total_nodes,result):
        if node not in unvisited_nodes:
            if node in result or node not in total_nodes:
                return True
            else:
                #Uh-oh, there was a cycle
                del result[:]
                result.append(node)
                return False
        else:
            unvisited_nodes.remove(node)
            for e in edges[node]:
                if not visit(e[0],edges,total_nodes,result):
                    if result[-1] != None:
                        if node in result:
                            result.append(None)
                        else:
                            result.append(node)
                    return False
            result.append(node)
            return True

    # Cleans up the return value to leave only numbered nodes
    def sanitize(retVal):
        return set(filter(lambda node: type(node) == int, retVal))


    # Topologically sort the class's local dependency graph using DFS
    ret = []
    while len(unvisited_nodes) > 0:
        n = next(iter(unvisited_nodes))
        if not visit(n,incoming,total_nodes,ret):
            return (False, sanitize(ret))

    return (True, map(lambda node: node_names[node] if type(node) == int else ('visit', node),ret))

