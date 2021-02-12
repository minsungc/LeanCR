import data.fintype.basic
import data.sym2

namespace my_section

variable x : nat

def bar : nat := x + 3

#check bar

end my_section

#check my_section.bar

open my_section

#check bar

section

variable x : list nat

def baz := x ++ x 

end

/-
Reflexive Graphs:
We define reflexive graphs as a reflexive symmetric relation on a vertex type 'V'.
-/
open finset
universe u

variables x y z : nat

def f : nat := x + 3

#eval f 2

def g := λ x, x + 3

example : f = g := rfl

#print f

def adj {V : Type} : V → V → Prop :=
λ u v, true

example : adj 2 3 :=
begin
  dsimp [adj],
  triv
end

example : adj 2 3 := trivial

#check nat
#check 2
#check (2 : nat)


structure foo (A : Type) : Type :=
(a : nat)
(b : nat)
(c : A)
(h : a + 3 < b)

def my_foo_thingy : foo nat :=
{ a := 4,
  b := 9,
  c := 3,
  h := by norm_num }

def type_example (A B : Type) : Type := A × B × B

#check foo nat
#check type_example nat nat

#check my_foo_thingy
#print my_foo_thingy

example : my_foo_thingy.a = 4 := rfl

#check foo

variable x : foo

#check x


def adj' (V : Type) (u v : V) : Prop :=
u = v

/-
begin
  intros u v,
  exact u = v
end 
-/

structure refl_graph (V : Type u) :=
(adj : V → V → Prop) /-Is this the adjacency relation? Vertex-> Vertex-> -/
(sym : symmetric adj . obviously)
(selfloop : reflexive adj . obviously)

def complete_refl_graph (V: Type u) : refl_graph V :=
{ adj := λ u v, true,
  sym := λ u v h, trivial,
  selfloop := λ u, trivial }

/-Need to define graph homomorphism. Not defined yet-/
structure graph_hom {V W : Type} (G: refl_graph V) (H: refl_graph W) :=
(to_fun : V → W)
(mapEdges: ∀ v w, G.adj v w → H.adj (to_fun v) (to_fun w))

structure cops_and_robbers_game :=
(V : Type)
(G : refl_graph V)
(num_cops : nat)
(robber_start : V)
(cops_start : fin num_cops → V)
(start_ok : ∀ i : fin num_cops, cops_start i ≠ robber_start)


section CR_graphs

parameters {V : Type u} (G : refl_graph V)

/-The definition of neighbor set was stolen from mathlib. Closed neighbor set is used to define corners, which is a central concept-/
def neighbor_set (v : V) : set V := set_of (G.adj v)
def neighbor_set' (v : V) : set V := { w | G.adj v w }


def closed_neighbor_set (v : V) : set V := (neighbor_set v) ∪ {v}

/-
Corner vertices, an important concept in Cops and Robbers
A vtx w is a corner iff there exists some vertex v such that the neighbors of w is a subset of the neighbors of v
-/
def corner_vtx (w: V) (S: set V) : Prop :=
  (∃ v ∈ S, closed_neighbor_set w ⊆ closed_neighbor_set v)


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
