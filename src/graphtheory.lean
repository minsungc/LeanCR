import data.fintype.basic
import data.sym2

/-
Reflexive Graphs:
We define reflexive graphs as a reflexive symmetric relation on a vertex type 'V'.
-/
open finset
universe u

structure refl_graph (V : Type u) :=
(adj : V → V → Prop) /-Is this the adjacency relation? Vertex-> Vertex-> -/
(sym : symmetric adj . obviously)
(selfloop : reflexive adj . obviously)

def complete_refl_graph (V: Type u) : refl_graph V :=
{ adj := V->V->true } /-Every vertex is related to each other, how to define?-/


/-Need to define graph homomorphism. Not defined yet-/
structure graph_hom (G: refl_graph V) (H: refl_graph W) :=
(to_fun G → H)
(mapEdges: ∀v w, G.adj v w → H.adj (to_fun v) (to_fun w))


section CR_graphs

parameters {V : Type u} (G : refl_graph V)

/-The definition of neighbor set was stolen from mathlib. Closed neighbor set is used to define corners, which is a central concept-/
def neighbor_set (v : V) : set V := set_of (G.adj v)
def closed_neighbor_set (v : V) : set V := (neighbor_set v) ∪ {v}

/-
Corner vertices, an important concept in Cops and Robbers
A vtx w is a corner iff there exists some vertex v such that the neighbors of w is a subset of the neighbors of v
-/
def corner_vtx (w: V) (S: set V) : Prop :=
  (∃ v ∈ S) (closed_neighbor_set w ⊆ closed_neighbor_set v)


/-
Retracts: A graph homomorphism where a we send a corner to the vertex it is cornered by, and everything else is identity
Setup: How should we define this? Thinking in terms of types, I was thinking something like Graph->Vertex->(Graph->Graph) (so it spits out a homomorphism), but it also might make sense to do something along the lines of Graph->Vertex->Graph (so it spits out the retracted graph).
-/
def retract (G: refl_graph V) (v: V) : sorry

/-
Dismantlable Graph: A graph where a succession of retracts will always lead to K_1
Needs some sort of recursive definition. Will look into this
-/
def dismantlable_graph 

/-
Goal for the near future: Prove the following lemma: 
Suppose there exists a dismantlable graph. Then the order in which the vertices are retracted form a partial order.
-/
lemma dism_graph_has_partial_order
end CR_graphs
