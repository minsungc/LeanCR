import data.fintype.basic
import data.sym2
import data.list

/-
Reflexive Graphs:
We define reflexive graphs as a reflexive symmetric relation on a vertex type 'V'.
-/
open finset

structure refl_graph (V: Type) :=
(adj : V → V → Prop) 
(sym : symmetric adj . obviously)
(selfloop : reflexive adj . obviously)

#check refl_graph

def complete_refl_graph (V: Type): refl_graph V :=
{ adj := λ u v, true,
  sym := λ u v h, trivial,
  selfloop := λ u, trivial }

/-Need to define graph homomorphism. Not defined yet-/
structure graph_hom {V W: Type} (G: refl_graph V) (H: refl_graph W) :=
(to_fun : V → W)
(mapEdges: ∀ v w, G.adj v w → H.adj (to_fun v) (to_fun w))

structure cr_game_init:=
(V : Type) 
(G : refl_graph V)
(num_cops : nat)
(robber_start : V)
(cops_start : vector V num_cops)
(start_ok : ∀ i : fin num_cops, vector.nth cops_start i ≠ robber_start)

#check list.tail
/-
Set up a cops and robber's game
-/
structure cr_game :=
(I: cr_game_init)
(cop_strat: vector I.V (I.num_cops)× I.V  → vector I.V (I.num_cops))
(cop_legal: ∀ i v P, I.G.adj (vector.nth P i) (vector.nth (cop_strat (P,v)) i))
(robber_strat: vector I.V (I.num_cops)× I.V → I.V)
(robber_legal: ∀ v P, I.G.adj v (robber_strat (P,v)))
(list_of_moves: list (vector I.V (I.num_cops)× I.V))
(cops_will_win: bool)

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

def retract (c:V) (v:V) (H: refl_graph V):=
let
K := refl_graph {v :V // v ≠ c}
in
graph_hom H K

def cop_win_graph (CR: cr_game):= (CR.I.num_cops=1) ∧ CR.cops_will_win

def dismantlable_graph := sorry

theorem cw_iff_dismantlable := sorry 
end CR_graphs
