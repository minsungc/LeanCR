import data.fintype.basic
import data.sym2

/-
Reflexive Graphs:
We define reflexive graphs as a reflexive symmetric relation on a vertex type 'V'.
-/
open finset

structure refl_graph (V: set Type) :=
(adj : Type → Type → Prop) 
(sym : ∀ x y ∈ V, adj x y ↔ adj y x . obviously)
(selfloop : reflexive adj . obviously)

def complete_refl_graph (V: set Type) : refl_graph V :=
{ adj := λ u v, true,
  sym := λ u v h, trivial,
  selfloop := λ u, trivial }

/-Need to define graph homomorphism. Not defined yet-/
structure graph_hom {V W : set Type} (G: refl_graph V) (H: refl_graph W) :=
(to_fun : Type → Type)
(mapEdges: ∀ v w, G.adj v w → H.adj (to_fun v) (to_fun w))

structure cr_game_init :=
(V : set Type)
(G : refl_graph V)
(num_cops : nat)
(robber_start : Type)
(cops_start : fin num_cops → V)
/-Read into why this doesn't typecheck-/
(start_ok : ∀ i : fin num_cops, robber_start ∉ cops_start i)

/-Issue: Want the cop and robber strategies domain to be I.V^(num_cops+1)-/
structure cr_game :=
(I: cr_game_init)
(cop_strat: vector I.V (I.num_cops+1)  → vector I.V (I.num_cops))
(robber_strat: vector I.V (I.num_cops+1) → I.V)
section CR_graphs

parameters {V W: set Type} (G : refl_graph V)

/-The definition of neighbor set was stolen from mathlib. Closed neighbor set is used to define corners, which is a central concept-/
def neighbor_set (v : Type) : set Type := set_of (G.adj v)
def closed_neighbor_set (v : V) : set V := (neighbor_set v) ∪ {v}

/-
Corner vertices, an important concept in Cops and Robbers
A vtx w is a corner iff there exists some vertex v such that the neighbors of w is a subset of the neighbors of v
-/
def corner_vtx (w: Type) (S: set Type) : Prop :=
  (∃ v ∈ S, closed_neighbor_set w ⊆ closed_neighbor_set v)

/-May need to restructure some things. We want to be able to add/subtract vertices of our graph. Maybe set?-/
structure retract (G: refl_graph V) (v: Type) (w: Type) :=
{corner_cndn: corner_vtx v V}
{retracted_graph: refl_graph V}
{retract_hom: graph_hom G retracted_graph}


end CR_graphs