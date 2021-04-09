import data.fintype.basic
import data.sym2
import data.list
import order.conditionally_complete_lattice
import system.random.basic


/-
Reflexive Graphs:
We define reflexive graphs as a reflexive symmetric relation on a vertex type 'V'.
-/
open finset
open classical

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

def equivgraph {V W: Type} (G  : refl_graph V) (H: refl_graph W)  : Prop := nonempty(graph_iso G H)

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

/-
Set up a cops and robber's game on a graph

MAYBE separate the cop and robber strategy? Would be easier doing the universal quantifiers in the long run
-/
structure cop_strat {V: Type} [fintype V] (G: refl_graph V) (n :ℕ ) :=
(cop_init:  vector V n)
(cop_strat: vector V n × V  → vector V n)
(cop_legal: ∀ i v P, G.adj (vector.nth P i) (vector.nth (cop_strat (P,v)) i))

structure rob_strat {V: Type} [fintype V] (G: refl_graph V) (n : ℕ ) :=
(rob_init: vector V n → V)
(rob_strat: vector V n× V → V)
(rob_legal: ∀ v P, G.adj v (rob_strat (P,v)))

def capture {V: Type} [fintype V] {k : ℕ } (P: vector V k × V) := ∃ i, vector.nth P.1 i = P.2

def round {V: Type} [fintype V] {G: refl_graph V} {k : ℕ } (CS: cop_strat G k) (RS: rob_strat G k) : ℕ → vector V k × V
| 0 := (CS.cop_init, RS.rob_init (CS.cop_init))
| (n+1) := (CS.cop_strat (round n), 
            RS.rob_strat(CS.cop_strat (round n), (round n).2) )

def winning_strat_cop {V: Type} [fintype V] {G: refl_graph V} {k :ℕ } 
(CS: cop_strat G k) := 
  ∀ RS: rob_strat G k , ∃ n : ℕ, capture (round CS RS n)

def k_cop_win {V: Type} [fintype V] (G: refl_graph V) (k: ℕ ) := 
∃ CS: cop_strat G k, winning_strat_cop CS

def winning_strat_rob {V: Type} [fintype V] {G: refl_graph V} {k : ℕ } 
(RS: rob_strat G k) := 
  ∀ CS: cop_strat G k, ∀ n : ℕ, not(capture (round CS RS n))

structure cr_game {V: Type} [fintype V] (G: refl_graph V) (n : ℕ ):=
(cop_strat: cop_strat G n)
(rob_strat: rob_strat G n)


def cop_number {V: Type} [fintype V] [has_Inf ℕ] (G: refl_graph V) := 
  Inf {k : ℕ | k_cop_win G k}

def cop_win_graph {V: Type} [fintype V] [has_Inf ℕ] (G: refl_graph V) := cop_number G = 1

---------------------------------------------------------------------------------------------------------
#check eq.symm
noncomputable def exists_list_of_elts (V: Type) [fintype V] [decidable_eq V]: vector V (fintype.card V):= 
begin
  choose L hL using fintype.exists_univ_list V,
  cases hL with h1 h2,
  have P: V ≃ (fin L.length),
    exact fintype.equiv_fin_of_forall_mem_list h2 h1,
  have Q: fintype.card (fin L.length) = fintype.card V,
    exact fintype.card_congr (equiv.symm P),
  have R: fintype.card (fin L.length) = L.length,
    exact fintype.card_fin (L.length),
  have S: fintype.card V = L.length,
    exact eq.trans (eq.symm Q) R,
  exact ⟨L, eq.symm S⟩,
end

def find_index {V: Type} (p : V → Prop) [decidable_pred p] : list V → ℕ → option ℕ 
| [] n    := none
| (a::l) n := if p a then some n else find_index l (n+1)

noncomputable def find_ind_vec {V: Type } [fintype V] [decidable_eq V] {n : ℕ } (vec: vector V n) (v: V) : ℕ :=
begin
  let L := vector.to_list vec,
  let p := λ x, x=v,
  let O := find_index p L 0,
  have S : option.is_some O = tt,
  {
    /-TODO-/
    sorry,
  },
  exact option.get S,
end

noncomputable def trivial_strategy {V: Type} [fintype V] [decidable_eq V] [has_Inf ℕ] (G: refl_graph V) : cop_strat G (fintype.card V) :=
{
  cop_init := exists_list_of_elts V,
  cop_strat:= λ x, x.1,
  cop_legal :=
    begin
      intros i v L,
      simp,
      apply G.selfloop,
    end,
}

lemma lots_of_cops {V: Type} [fintype V] [has_Inf ℕ] [decidable_eq V] (G: refl_graph V) : 
V ≠ empty  → set.nonempty {k : ℕ | k_cop_win G k} :=
begin
  intro non,
  let strat_all := trivial_strategy G,
  have con: (fintype.card V) ∈ {k : ℕ | k_cop_win G k},
  {
    use strat_all,
    rw winning_strat_cop,
    intro RS,
    use 0,
    rw capture,
    /-TODO-/
    sorry,
  },
  rwa set.nonempty_def,
  use fintype.card V,
  exact con,
end

#check nat.Inf_eq_zero.1
lemma zero_cops_cant_win {V: Type} [fintype V] [has_Inf ℕ] [decidable_eq V] :
  V ≠ empty → ∀ G : refl_graph V, 0<cop_number G :=
begin
  intro non,
  intro G,
  by_contradiction H,
  rw not_lt at H,
  have zero_cops: cop_number G = 0,
  {
    have h: cop_number G ≤ 0 → cop_number G = 0,
      simp,
    exact h H,
  },
  rw cop_number at zero_cops,
  have Inf_zero : 0 ∈ {k : ℕ | k_cop_win G k} ∨ {k : ℕ | k_cop_win G k} = ∅,
  {
    sorry,
  },
  cases Inf_zero with H1 H2,
  {
    sorry,
  },
  {
    let K := lots_of_cops G non,
    have negK : ¬ {k : ℕ | k_cop_win G k}.nonempty,
    {
      sorry,
    }
  },
  -- apply (nat.Inf_eq_zero).1 zero_cops,
  /-Proof outline: 
  Suppose cop number of G=0. 
  Then G has a winning strategy with 0 cops.
  Then for all robber strats, the cops will eventually capture the robber.
  However consider the robber strategy where it goes on a vtx and doesn't move (uses nonempty)
  Then for all natural numbers, the cop cannot capture the robber.
  So this was not a winning strategy.
  -/
end

def complete_strategy (V: Type) [fintype V] [decidable_eq V] [inhabited V] [has_Inf ℕ] : cop_strat (complete_refl_graph V) 1 :=
{
  cop_init := 
  begin
  let v := arbitrary V,
    let L := [v],
  have prop: L.length = 1,
  {
    simp,
  },
  exact ⟨L, prop⟩, 
  end,
  cop_strat:= 
  begin
    intro x,
    let L := [x.2],
    have prop: L.length = 1,
    {
      simp,
    },
    exact ⟨L, prop⟩, 
  end, 
  cop_legal := 
  begin
    intros i v P,
    simp,
  end
}

lemma complete_refl_graph_cop_win (V: Type) [fintype V][decidable_eq V] [inhabited V]  [has_Inf ℕ] : V ≠ empty → cop_win_graph (complete_refl_graph V) :=
begin
  rw cop_win_graph,
  rw cop_number,
  intro non,
  have CW : 1 ∈ {k : ℕ | k_cop_win (complete_refl_graph V) k},
  {
    let CW_strat := complete_strategy V,
    have winning : winning_strat_cop CW_strat,
    {
      intro RS,
      use 1,
      use 0,
      unfold round,
      simp,
      sorry,
    },
    simp,
    use CW_strat,
    exact winning,
  },
  /-
  Proof outline:
  We want to find a winning cop strategy for a complete graph.
  Define the cop strategy as follows:
  cop_init: [v] for some arbitrary v : V
  cop_strat: (v,w) → w
  cop_legal : uses the fact that the graph is complete_refl_graph
  So the cop number is 1 or 0.
  The cop number can't be 0 because zero_cops_cant_win.
  So the cop number is 1.
  -/
end

---------------------------------------------------------------------------------------------------
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

def is_corner (v: V) (G: refl_graph V) : Prop := (has_corner G) ∧ corner_vtx v 

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
