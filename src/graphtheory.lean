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


#check refl_graph.sym

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

def cat_prod_graph {V W: Type} (G: refl_graph V) (H: refl_graph W) : refl_graph (V × W) :=
{
  adj := λ u v, (G.adj u.1 v.1) ∧ (H.adj u.2 v.2),
  sym :=
  begin
    intros u v,
    intros h,
/-QUESTION: If we flip lines 43 and 44 we get error. Why?-/
    cases h with Gedge Hedge,
    split,
    exact G.sym Gedge,
    exact H.sym Hedge,
  end,
  selfloop:=
  begin
    intro x,
    split,
    exact G.selfloop x.1,
    exact H.selfloop x.2,
  end
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

structure graph_iso {V W: Type} (G  : refl_graph V) (H: refl_graph W) :=
(to_fun : V → W)
(bij: function.bijective to_fun)
(mapEdges: ∀ v w, G.adj v w ↔ H.adj (to_fun v) (to_fun w))

def equivgraph {V W: Type} (G  : refl_graph V) (H: refl_graph W)  : Prop := ∃ a, a = graph_iso G H

notation G `≅` H  := equivgraph G H

def identity_iso {V: Type} (G: refl_graph V) : graph_iso G G:=
{
  to_fun:= λ x,x,
  bij:= 
    begin
      unfold function.bijective,
      split, 
      {
        intros x y,
        intros h,
        apply h,
      },
      {
        intro x,
        use x,
      },
    end,
  mapEdges:=
    begin
      intros v w,
      split,
      { intro h, exact h},
      { intro h, exact h}
    end
}
def trivial_iso : graph_iso empty_graph empty_graph := identity_iso empty_graph

lemma isos_are_comm {V W: Type} {G  : refl_graph V} {H: refl_graph W} : cat_prod_graph G H ≅ cat_prod_graph H G :=
begin
  /-TODO-/
end

variable n: ℕ
/-
Set up a cops and robber's game on a graph

MAYBE separate the cop and robber strategy? Would be easier doing the universal quantifiers in the long run
-/
structure cop_strat {V: Type} [fintype V] (G: refl_graph V) (n : fin (fintype.card V+1)) :=
(cop_init:  vector V n)
(cop_strat: vector V n × V  → vector V n)
(cop_legal: ∀ i v P, G.adj (vector.nth P i) (vector.nth (cop_strat (P,v)) i))

structure rob_strat {V: Type} [fintype V] (G: refl_graph V) (n : fin (fintype.card V+1)) :=
(rob_init: vector V n → V)
(rob_strat: vector V n× V → V)
(rob_legal: ∀ v P, G.adj v (rob_strat (P,v)))

def capture {V: Type} [fintype V] {k : fin (fintype.card V+1)} (P: vector V k × V) := ∃ i, vector.nth P.1 i = P.2

def round {V: Type} [fintype V] {G: refl_graph V} {k : fin (fintype.card V+1)} (CS: cop_strat G k) (RS: rob_strat G k) : ℕ → vector V k × V
| 0 := (CS.cop_init, RS.rob_init (CS.cop_init))
| (n+1) := (CS.cop_strat (round n), 
            RS.rob_strat(CS.cop_strat (round n), (round n).2) )

def winning_strat_cop {V: Type} [fintype V] {G: refl_graph V} {k : fin (fintype.card V+1)} 
(CS: cop_strat G k) := 
  ∀ RS: rob_strat G k , ∃ n : ℕ, capture (round CS RS n)

def k_cop_win {V: Type} [fintype V] (G: refl_graph V) (k: fin (fintype.card V+1)) := 
∃ CS: cop_strat G k, winning_strat_cop CS

def winning_strat_rob {V: Type} [fintype V] {G: refl_graph V} {k : fin (fintype.card V+1)} 
(RS: rob_strat G k) := 
  ∀ CS: cop_strat G k, not (∃ n : ℕ, capture (round CS RS n))

structure cr_game {V: Type} [fintype V] (G: refl_graph V) (n : fin (fintype.card V+1)):=
(cop_strat: cop_strat G n)
(rob_strat: rob_strat G n)
(someone_wins: xor (winning_strat_cop cop_strat) (winning_strat_rob rob_strat))

def cop_number {V: Type} [fintype V] [has_Inf ℕ] (G: refl_graph V) := 
  Inf {k : ℕ | k_cop_win G k}

def cop_win_graph {V: Type} [fintype V] [has_Inf ℕ] (G: refl_graph V) := cop_number G = 1

section CR_graphs

parameters {V W: Type}[fintype V] (G : refl_graph V)

/-The definition of neighbor set was stolen from mathlib. Closed neighbor set is used to define corners, which is a central concept-/
def neighbor_set (v : V) : set V := set_of (G.adj v)
def neighbor_set' (v : V) : set V := { w | G.adj v w }

def closed_neighbor_set (v : V) : set V := (neighbor_set v) ∪ {v}
/-
Corner vertices, an important concept in Cops and Robbers
A vtx w is a corner iff there exists some vertex v such that the neighbors of w is a subset of the neighbors of v
-/
def corner_vtx (w: V)  : Prop :=
  (∃ v , closed_neighbor_set w ⊆ closed_neighbor_set v)

def has_corner (G: refl_graph V) : Prop :=
  (∃ w , corner_vtx w)

/-Question: Why is univ defined as a finset-/
#check univ

#check some
def is_corner (v: V) (G: refl_graph V) : Prop := (has_corner G) ∧ corner_vtx v 
def find_corner (G: refl_graph V) : option V := if ∃ v, is_corner v G then some v else none

/-TODO: This theorem. It uses the "second to last" move of the cop, which might be a little hard to encode-/
theorem cwg_has_corner [decidable_eq V] [has_Inf ℕ] (G: refl_graph V): cop_win_graph G → has_corner G := 
begin
  intro h,
  sorry,
end

lemma edge_symm (u v : V) : G.adj u v ↔  G.adj v u := ⟨λ x, G.sym x, λ y, G.sym y⟩
 
def rm_graph (c: V) (H: refl_graph V) : refl_graph {v:V//v ≠ c} :=
{ adj := λ a b, H.adj a b, 
  sym :=  λ a b h, H.sym h,
  selfloop := 
  begin
    intro a, 
    apply H.selfloop,
  end  
}

structure retract (c:V) (v:V) (H: refl_graph V):=
(f: graph_hom H (rm_graph c H)) 
(is_retract:  ↑(f.to_fun c) = v )

def dismantle (G: refl_graph V) : list V → Prop
| [] := G ≅ singleton_graph 
| (a::L) := (is_corner a G) ∧ dismantle L

def dismantlable_graph (G: refl_graph V) := ∃ L, dismantle G L


end CR_graphs
