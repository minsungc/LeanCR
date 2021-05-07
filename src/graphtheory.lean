import data.fintype.basic
import data.sym2
import data.list
import data.set.basic
import order.conditionally_complete_lattice
import system.random.basic


/-
Reflexive Graphs:
We define reflexive graphs as a refstraAlexive symmetric relation on a vertex type 'V'.
-/
open finset
open classical

structure refl_graph (V: Type):=
(adj : V → V → Prop) 
(sym : symmetric adj)
(selfloop : reflexive adj . obviously)

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
-/
def capture {V: Type} [fintype V] {k : ℕ } (P: vector V k × V) := ∃ i, vector.nth P.1 i = P.2

structure cop_strat {V: Type} [fintype V] (G: refl_graph V) (n :ℕ ) :=
(cop_init:  vector V n)
(cop_strat: vector V n × V  → vector V n)
(cop_nocheat: ∀ V v, capture (V,v) → cop_strat (V,v) = V)
(cop_legal: ∀ i v P, G.adj (vector.nth P i) (vector.nth (cop_strat (P,v)) i))
/-Cop doesnt sabotage himself-/

structure rob_strat {V: Type} [fintype V] (G: refl_graph V) (n : ℕ ) :=
(rob_init: vector V n → V)
(rob_strat: vector V n× V → V)
(rob_nocheat: ∀ K,  capture K → rob_strat K = K.2)
(rob_legal: ∀ v P, G.adj v (rob_strat (P,v)))


def round {V: Type} [fintype V] {G: refl_graph V} {k : ℕ } (CS: cop_strat G k) (RS: rob_strat G k) : ℕ → vector V k × V
| 0 := (CS.cop_init, RS.rob_init (CS.cop_init))
| (n+1) := (CS.cop_strat (round n), 
            RS.rob_strat(CS.cop_strat (round n), (round n).2))

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
noncomputable theory
def enum_elts (V: Type) [fintype V] [decidable_eq V]: fin (fintype.card V) ≃ V :=
(fintype.equiv_fin V).out.symm

lemma exists_index {V: Type} [fintype V] [decidable_eq V] (v : V)  : ∃ i, enum_elts V i = v :=
(enum_elts V).bijective.surjective v

lemma exists_index_vec {V: Type} [fintype V] [decidable_eq V] (v: V) : ∃ i, vector.nth (vector.of_fn (enum_elts V)) i = v :=
begin
  cases exists_index v with i hi, 
  use i,
  simp,
  exact hi,
end

/-TODO: Two cops on the same vector?-/
def trivial_strategy {V: Type} [fintype V] [decidable_eq V] (G: refl_graph V) : cop_strat G (fintype.card V) :=
{
  cop_init :=  vector.of_fn (enum_elts V),
  cop_strat:= λ x, x.1,
  cop_nocheat :=
    begin
      intros V v hyp,
      refl,
    end,
  cop_legal :=
    begin
      intros i v L,
      simp,
      apply G.selfloop,
    end,
}

lemma lots_of_cops {V: Type} [fintype V] [decidable_eq V] [inhabited V] (G: refl_graph V) : 
set.nonempty {k : ℕ | k_cop_win G k} :=
begin
  let strat_all := trivial_strategy G,
  have con: (fintype.card V) ∈ {k : ℕ | k_cop_win G k},
  {
    use strat_all,
    rw winning_strat_cop,
    intro RS,
    use 0,
    rw capture,
    let v := (round strat_all RS 0).snd,
    exact exists_index_vec v,
  },
  rwa set.nonempty_def,
  use fintype.card V,
  exact con,
end

def zero_cop_robber_strategy {V: Type} [fintype V] [decidable_eq V] [inhabited V] [decidable_eq V] (G: refl_graph V): rob_strat G 0 :=
{
  rob_init:= λ x, arbitrary V,
  rob_strat := λ x, x.2,
  rob_nocheat :=
  begin
    intros K C,
    refl,
  end,
  rob_legal :=
  begin
    simp,
    intros v H,
    apply G.selfloop,
  end
}

lemma zero_cops_cant_win {V: Type} [fintype V] [decidable_eq V][inhabited V]  :
  ∀ G : refl_graph V, 0<cop_number G :=
begin
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
    apply (nat.Inf_eq_zero).1 zero_cops,
  cases Inf_zero with H1 H2,
  { have zero_win : k_cop_win G 0,
      apply' H1,
    rw k_cop_win at zero_win,
    have not_zero_win: ¬ (∃ (CS : cop_strat G 0), winning_strat_cop CS),
    { push_neg,
      intro CS,
      rw winning_strat_cop,
      push_neg,
      let RS := zero_cop_robber_strategy G,
      use RS,
      intro n,
      cases n,
      { rw capture,
        simp,
        intro x,
        apply fin.elim0 x, },
      { rw capture,
        simp,
        intro x,
        apply fin.elim0 x,},},
    contradiction,},
  { let K := lots_of_cops G,
    have negK : ¬ set.nonempty {k : ℕ | k_cop_win G k},
    { rw H2,
      exact not_nonempty_empty,},
    contradiction,},
  -- ,
end

lemma zero_cops_cant_win' {V: Type} [fintype V] [decidable_eq V][inhabited V]  :
  ∀ G : refl_graph V, 0<cop_number G :=
begin
  intro G,
  apply nat.pos_of_ne_zero,
  intro zero_cops,
  cases nat.Inf_eq_zero.mp zero_cops with H1 H2,
  { cases H1 with CS WCS,
    specialize WCS (zero_cop_robber_strategy G),
    rcases WCS with ⟨n, ⟨x, _⟩⟩,
    exact fin.elim0 x},
  cases lots_of_cops G with x h,
  rw H2 at h,
  exact set.not_mem_empty _ h,
end


def complete_strategy (V: Type) [fintype V] [decidable_eq V] [inhabited V] : cop_strat (complete_refl_graph V) 1 :=
{ cop_init  := ⟨[arbitrary V], rfl⟩,
  cop_strat := λ x, ⟨[x.2], rfl⟩,
  cop_nocheat :=
    begin
      intros V1 v hyp,
      simp,
      rw capture at hyp,
      simp at hyp,
      cases hyp with i hyp',
      have this: i=0,
        simp,
      rw this at hyp',
      refine vector.ext _,
      intro m,
      have this: m=0,
        simp,
      rwa this,
      rwa hyp', refl,
    end,
  cop_legal := λ i v p, trivial }

lemma complete_refl_graph_cop_win (V: Type) [fintype V][decidable_eq V] [inhabited V] : cop_win_graph (complete_refl_graph V) :=
begin
  rw cop_win_graph,
  rw cop_number,
  have CW : 1 ∈ {k : ℕ | k_cop_win (complete_refl_graph V) k},
  {
    let CW_strat := complete_strategy V,
    have winning : winning_strat_cop CW_strat,
    {
      intro RS,
      use 1,
      use 0,
      let I := round CW_strat RS 0,
      have cap: capture (CW_strat.cop_strat I,I.2),
      {
        unfold capture,
        use 0,
        simp,
        refl,
      },
      have eq: I.2 = (round CW_strat RS 1).1.nth 0,
      {
        unfold round,
        simp,
        refl,
      },
      have eq' : I.2 = (round CW_strat RS 1).2,
      {
        unfold round,
        simp,
        let C:= RS.rob_nocheat (CW_strat.cop_strat I,I.2) cap,
        exact C.symm,
      }, 
      exact trans (symm eq) eq',
    },
    simp,
    use CW_strat,
    exact winning,
  },
  have leq: Inf {k : ℕ | k_cop_win (complete_refl_graph V) k} ≤ 1,
    exact nat.Inf_le CW,
  have ge : Inf {k : ℕ | k_cop_win (complete_refl_graph V) k} >0,
    exact zero_cops_cant_win (complete_refl_graph V),
  linarith,
end

lemma complete_refl_graph_cop_win' (V: Type) [fintype V] [decidable_eq V] [inhabited V] : cop_win_graph (complete_refl_graph V) :=
begin
  rw [cop_win_graph, cop_number],
  have leq: Inf {k : ℕ | k_cop_win (complete_refl_graph V) k} ≤ 1,
  { apply nat.Inf_le,
    use [complete_strategy V],
    intro RS,
    use [1, 0],
    symmetry, transitivity, apply RS.rob_nocheat,
    { use [0, rfl] },
    refl },
  have ge : Inf {k : ℕ | k_cop_win (complete_refl_graph V) k} > 0,
    exact zero_cops_cant_win (complete_refl_graph V),
  linarith,
end
