interface Top {}
interface Node {
    var a : int;
    var b : int;
    var c : int;
    var d : int;
}

class Root : Top {
    children {
        child : Node;
    }
    actions {
        child.a := child.b;
        child.c := child.a;
    }
}

class MidNode : Node {
    children {
        child1 : Node;
        child2 : Node;
    }
    actions {
        child1.a := a;
        child2.a := a;
        b := child1.b + child2.b;
        child1.c := c;
        child2.c := child1.d;
        d := child2.d;
    }
}

class Leaf : Node {
    actions {
        b := 0;
        d := c;
    }
}
