import data.fintype.basic
import data.sym2
import data.list

/-
Reflexive Graphs:
We define reflexive graphs as a reflexive symmetric relation on a vertex type 'V'.
-/
open finset

structure refl_graph (V: Type):=
(adj : V → V → Prop) 
(sym : symmetric adj)
(selfloop : reflexive adj . obviously)


#check refl_graph

def complete_refl_graph (V: Type) : refl_graph V :=
{ adj := λ u v, true,
  sym := λ u v h,  trivial ,
  selfloop := λ u, trivial }


def empty_graph : refl_graph empty :=
/-complete_refl_graph empty-/
{
  adj := λ u v, true,
  sym := λ u v h, trivial,
  selfloop := λ u, trivial
}

def singleton_graph :refl_graph unit := complete_refl_graph unit

/-Need to define graph homomorphism. Not defined yet-/
structure graph_hom {V W: Type} (G  : refl_graph V) (H: refl_graph W) :=
(to_fun : V → W)
(mapEdges: ∀ v w, G.adj v w → H.adj (to_fun v) (to_fun w))

def graph_hom_comp {U V W : Type} {G: refl_graph U} {H: refl_graph V} {I: refl_graph W} 
  (f: graph_hom G H) (g: graph_hom H I) : graph_hom G I :=
{
  to_fun := g.to_fun ∘ f.to_fun ,
  mapEdges := 
  begin
    intros u v,
    intro h,
    have adj_H : H.adj (f.to_fun u) (f.to_fun v),
      exact f.mapEdges u v h,
    exact g.mapEdges (f.to_fun u) (f.to_fun v) adj_H,
  end 
}

def trivial_hom {V:Type} (G: refl_graph V) : graph_hom G G :=
{
  to_fun := λ x, x,
  mapEdges :=
  begin
    intros u v h, 
    exact h,
  end
}

structure cr_game_init (V: Type) [fintype V]:=
(G: refl_graph V)
(num_cops : nat)
(robber_start : V)
(cops_start : vector V num_cops)
(start_ok : ∀ i : fin num_cops, vector.nth cops_start i ≠ robber_start)

/-
Set up a cops and robber's game
-/

structure cr_game (V: Type) [fintype V]:=
(I: cr_game_init V)
(cop_strat: vector V (I.num_cops)× V  → vector V (I.num_cops))
(cop_legal: ∀ i v P, I.G.adj (vector.nth P i) (vector.nth (cop_strat (P,v)) i))
(robber_strat: vector V (I.num_cops)× V → V)
(robber_legal: ∀ v P, I.G.adj v (robber_strat (P,v)))
(list_of_moves: list (vector V (I.num_cops)× V))
(list_is_valid: list (vector V (I.num_cops)× V) → bool
  | [] := true
  | [a] := true
  | (b::(c::L)) := (cop_strat b, robber_strat b)=c) ∧ list_is_valid(c::L))

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

lemma edge_symm (u v : V) : G.adj u v ↔  G.adj v u := ⟨λ x, G.sym x, λ y, G.sym y⟩
 
def rm_graph (c: V) (H: refl_graph V) : refl_graph {v:V//v ≠ c} :=
{ adj := λ a b, H.adj a b, 
  sym :=  λ a b h, H.sym h
  /- begin
   intros a b,
   intro h,
   apply H.sym,
   apply h,
  end-/
  ,
  selfloop := 
  begin
    intro a, 
    apply H.selfloop,
  end  
}

structure retract (c:V) (v:V) (H: refl_graph V):=
(f: graph_hom H (rm_graph c H))
(is_retract:  ↑(f.to_fun c) = v)

def cop_win_graph (CR: cr_game):= (CR.I.num_cops=1) ∧ CR.cops_will_win

def dismantlable_graph := sorry

theorem cw_iff_dismantlable := sorry 

end CR_graphs
