vertex(9,root,a,child).
vertex(7,root,b,child).
vertex(8,root,c,child).
vertex(6,root,d,child).

vertex(2,midnode,a,self).
vertex(3,midnode,b,self).
vertex(1,midnode,c,self).
vertex(1,midnode,d,self).

vertex(2,midnode,a,child1).
vertex(3,midnode,b,child1).
vertex(1,midnode,c,child1).
vertex(1,midnode,d,child1).

vertex(2,midnode,a,child2).
vertex(3,midnode,b,child2).
vertex(1,midnode,c,child2).
vertex(1,midnode,d,child2).

vertex(5,leaf,a,self).
vertex(4,leaf,b,self).
vertex(1,leaf,c,self).
vertex(1,leaf,d,self).

edgeraw(midnode,child2,d,midnode,self,d,local).
edgeraw(midnode,self,c,midnode,child1,c,local).
edgeraw(midnode,child1,d,midnode,child2,c,local).
edgeraw(midnode,child1,c,midnode,self,c,inherited).
edgeraw(midnode,child1,c,leaf,self,c,inherited).
edgeraw(midnode,child2,c,leaf,self,c,inherited).
edgeraw(midnode,child2,c,midnode,self,c,inherited).
edgeraw(midnode,self,d,midnode,child1,d,synthesized).
edgeraw(midnode,self,d,midnode,child2,d,synthesized).
edgeraw(leaf,self,d,midnode,child1,d,synthesized).
edgeraw(leaf,self,d,midnode,child2,d,synthesized).
edgeraw(leaf,self,c,leaf,self,d,local).

edgeraw(midnode,self,a,midnode,child1,a,local).
edgeraw(midnode,self,a,midnode,child2,a,local).
edgeraw(midnode,child1,a,midnode,self,a,inherited).
edgeraw(midnode,child2,a,midnode,self,a,inherited).

edgeraw(midnode,child1,b,midnode,self,b,local).
edgeraw(midnode,child2,b,midnode,self,b,local).
edgeraw(midnode,self,b,midnode,child1,b,synthesized).
edgeraw(midnode,self,b,midnode,child2,b,synthesized).

edgeraw(midnode,self,d,root,child,d,synthesized).
edgeraw(leaf,self,d,root,child,d,synthesized).
edgeraw(midnode,self,b,root,child,b,synthesized).
edgeraw(leaf,self,b,root,child,b,synthesized).
edgeraw(root,child,c,midnode,self,c,inherited).
edgeraw(root,child,c,leaf,self,c,inherited).
edgeraw(root,child,a,midnode,self,a,inherited).
edgeraw(root,child,a,leaf,self,a,inherited).
edgeraw(root,child,b,root,child,a,local).
edgeraw(root,child,a,root,child,c,local).
edgeraw(midnode,child1,a,leaf,self,a,inherited).
edgeraw(midnode,child2,a,leaf,self,a,inherited).
edgeraw(leaf,self,b,midnode,child1,b,synthesized).
edgeraw(leaf,self,b,midnode,child2,b,synthesized).

edge(0, Class1, Attr1,Child1, Class2, Attr2,Child2, Type) :-
    vertex(SCC1,Class1,Attr1,Child1), vertex(SCC2,Class2,Attr2,Child2),
    edgeraw(Class1,Child1,Attr1,Class2,Child2,Attr2,Type), not(SCC1 = SCC2).

edge(Component, Class1,Attr1,Child1, Class2, Attr2,Child2, Type) :-
    vertex(Component,Class1,Attr1,Child1), vertex(Component,Class2,Attr2,Child2),
    edgeraw(Class1,Child1,Attr1,Class2,Child2,Attr2,Type).


tvalid(Component,local,C,A,Ch) :- tcomputable(Component,C,A,Ch).

tcomputable(Component,Class,Attr,Child) :- forall(
    edge(Component,CStart,AStart,ChStart,Class,Attr,Child,T),
    tvalid(Component,T,CStart,AStart,ChStart)
).

trivial(Component) :- forall(
    vertex(Component,Class,Attr,Child),
    tcomputable(Component,Class,Attr,Child)
).

tdvalid(_,inherited,_,_,_).
tdvalid(Component,local,C,A,Ch) :- tdcomputable(Component,C,A,Ch).

tdcomputable(Component,Class,Attr,Child) :- forall(
    edge(Component,CStart,AStart,ChStart,Class,Attr,Child,T),
    tdvalid(Component,T,CStart,AStart,ChStart)
).

td(Component) :- forall(
    vertex(Component,Class,Attr,Child),
    tdcomputable(Component,Class,Attr,Child)
).


buvalid(_,synthesized,_,_,_).
buvalid(Component,local,C,A,Ch) :- bucomputable(Component,C,A,Ch).

bucomputable(Component,Class,Attr,Child) :- forall(
    edge(Component,CStart,AStart,ChStart,Class,Attr,Child,T),
    buvalid(Component,T,CStart,AStart,ChStart)
).

bu(Component) :- forall(
    vertex(Component,Class,Attr,Child),
    bucomputable(Component,Class,Attr,Child)
).

inordervalid(_,inherited,_,_,_).
inordervalid(Component,local,CStart,AStart,ChStart) :- inordercomputable(Component,CStart,AStart,ChStart).
inordervalid(Component,synthesized,Class,_,Child) :- visit(Component,Class,Child).

visit(Component,Class,Child) :- forall(
    edge(Component,Class,AStart,Child,_,_,_,inherited),
    inordercomputable(Component,Class,AStart,Child)
).

inordercomputable(Component,Class,Attr,Child) :- forall(
    edge(Component,CStart,AStart,ChStart,Class,Attr,Child,T),
    inordervalid(Component,T,CStart,AStart,ChStart)
).

inorder(Component) :- forall(
    vertex(Component,Class,Attr,Child),
    inordercomputable(Component,Class,Attr,Child)
).

hasSynthesized(Component) :- edge(Component,_,_,_,_,_,_,synthesized).
hasInherited(Component) :- edge(Component,_,_,_,_,_,_,inherited).

type(Component,inorder) :- inorder(Component).
type(Component,td) :- bu(Component).
type(Component,bu) :- td(Component).
type(Component,trivial) :- trivial(Component).

metaEdge(C1,C2,T) :- vertex(C1,Class1,Attr1,Child1), vertex(C2,Class2,Attr2,Child2), edge(0,Class1,Attr1,Child1,Class2,Attr2,Child2,T).

canMerge(C1,C2,trivial,trivial) :- not(metaEdge(C1,C2,inherited)), not(metaEdge(C1,C2,synthesized)), trivial(C2).

canMerge(C1,C2,trivial,bu) :- not(metaEdge(C1,C2,inherited)), bu(C2).
canMerge(C1,C2,bu,bu) :- not(metaEdge(C1,C2,inherited)), bu(C2).

canMerge(C1,C2,trivial,td) :- not(metaEdge(C1,C2,synthesized)), td(C2).
canMerge(C1,C2,td,td) :- not(metaEdge(C1,C2,synthesized)), td(C2).

canMerge(C1,C2,trivial,inorder) :- not(metaEdge(C1,C2,synthesized)), inorder(C2).
canMerge(C1,C2,td,inorder) :- not(metaEdge(C1,C2,synthesized)), inorder(C2).
canMerge(C1,C2,td,inorder) :- bu(C2).
canMerge(C1,C2,inorder,inorder) :- not(metaEdge(C1,C2,inherited)), bu(C2).

source(C) :- vertex(C,_,_,_), not(metaEdge(_,C,_)).
sources(R) :- setof(C, source(C), R).

greedyScheduler(R) :- sources(S), runGreedyScheduler(S,S,R).

runGreedyScheduler(T,[],Seen,(T,Seen)).
runGreedyScheduler(TypeIn,Boundary,Seen,R) :- allNeighbors(Boundary,Seen,N,TypeIn,T), ord_union(Boundary,Seen,X),ord_union(N,X,Y), runGreedyScheduler(T,N,Y,R).

allNeighbors([],_,[],T,T).
allNeighbors([Node|Tail],Sources,Neighbors,Tin,Tout) :- 
    getNeighbors(Node,Sources,X,Tin,Ttmp), 
    allNeighbors(Tail,Sources,Y,Ttmp,Tout),
    ord_union(X,Y,Neighbors).

getNeighbors(C,Sources,Neighbors,Tin,Tout) :- setof(CNext,validNeighbor(C,Sources,CNext),X) *-> Neighbors=X; Neighbors=[].

member(X, [X|_]).
member(X, [_|T]) :- member(X,T).

validNeighbor(C,Sources,N) :- metaEdge(C,N,_),
    forall(
        metaEdge(Source,N,_),
        (member(Source, Sources),canMerge(Source,N,T))
    ).
