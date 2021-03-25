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
(F: graph_hom G H)
(bij: function.bijective F.to_fun)

/-
Set up a cops and robber's game on a graph
-/
structure cr_game_init {V: Type} [fintype V] (G: refl_graph V):=
(num_cops : nat)
(robber_start : V)
(cops_start : vector V num_cops)
(start_ok : ∀ i : fin num_cops, vector.nth cops_start i ≠ robber_start)

structure cr_game {V: Type} [fintype V] (G: refl_graph V):=
(I: cr_game_init G)
(cop_strat: vector V (I.num_cops)× V  → vector V (I.num_cops))
(cop_legal: ∀ i v P, G.adj (vector.nth P i) (vector.nth (cop_strat (P,v)) i))
(robber_strat: vector V (I.num_cops)× V → V)
(robber_legal: ∀ v P, G.adj v (robber_strat (P,v)))

/-
Trying to define what it means for a cop/robber to win 
-/
def cycle {V: Type} [fintype V] {G: refl_graph V} (CR : cr_game G) : vector V (CR.I.num_cops)× V → vector V (CR.I.num_cops)× V := 
 λ x, (CR.cop_strat x, CR.robber_strat (CR.cop_strat x, x.2))

def iter :  ℕ → (Type → Type) → (Type → Type) 
| 0 f := id
| 1 f := f 
| (n+1) f := f ∘ (iter n f) 

def cops_win {V: Type} [fintype V] [decidable_eq V] {G: refl_graph V} (CR : cr_game G) : Prop :=  
  ∃ n ∈ ℕ, ∃ m ≤ CR.I.num_cops, 
    vector.nth (iter n (cycle CR) (CR.I.cops_start, CR.I.robber_start)).1 m 
    = (iter n (cycle CR) (CR.I.cops_start, CR.I.robber_start)).2
 
def robbers_win {V: Type} [fintype V] [decidable_eq V] {G: refl_graph V} (CR : cr_game G) : Prop := 
  ¬ cops_win CR

/-
Defining cop number
-/
def cop_number {V: Type} [fintype V] (G: refl_graph V) := sorry

def cop_win_graph {V: Type} [fintype V] (G: refl_graph V): Prop := cop_number G = 1

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

def has_corner (G: refl_graph V) : Prop :=
  (∃ w , corner_vtx w (neighbor_set w) )

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
(is_retract:  ↑(f.to_fun c) = v )



end CR_graphs
