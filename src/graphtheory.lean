import data.fintype.basic
import data.sym2

/-
Reflexive Graphs:
We define reflexive graphs as a reflexive symmetric relation on a vertex type 'V'.
-/
open finset

structure refl_graph (V : Type) :=
(adj : V → V → Prop) 
(sym : symmetric adj . obviously)
(selfloop : reflexive adj . obviously)

def complete_refl_graph (V: Type) : refl_graph V :=
{ adj := λ u v, true,
  sym := λ u v h, trivial,
  selfloop := λ u, trivial }

/-Need to define graph homomorphism. Not defined yet-/
structure graph_hom {V W : Type} (G: refl_graph V) (H: refl_graph W) :=
(to_fun : V → W)
(mapEdges: ∀ v w, G.adj v w → H.adj (to_fun v) (to_fun w))

structure cr_game_init :=
(V : Type)
(G : refl_graph V)
(num_cops : nat)
(robber_start : V)
(cops_start : fin num_cops → V)
(start_ok : ∀ i : fin num_cops, cops_start i ≠ robber_start)

/-
Set up a cops and robber's game
-/
structure cr_game :=
(I: cr_game_init)
(cop_strat: vector I.V (I.num_cops+1)  → vector I.V (I.num_cops))
(robber_strat: vector I.V (I.num_cops+1) → I.V)


section CR_graphs

parameters {V W: Type} (G : refl_graph V)

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

def retract (v: V) (w: V) (G: refl_graph V) := sorry

end CR_graphs
