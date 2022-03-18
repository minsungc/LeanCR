import data.fintype.basic
import data.sym.sym2
import data.list
import data.set.basic
import order.conditionally_complete_lattice
import init.logic
import init.data.nat
import data.nat.lattice
import data.nat.parity


/-
Reflexive Graphs:
We define reflexive graphs as a refstraAlexive symmetric relation on a vertex type 'V'.
-/
open finset
open classical

noncomputable theory
open_locale classical

structure refl_graph (V: Type):=
(adj : V → V → Prop) 
(sym : symmetric adj)
(selfloop : reflexive adj . obviously)

def get_vtxs {V: Type} (G: refl_graph V) : Type := V

def complete_refl_graph (V: Type) : refl_graph V :=
{ adj := λ u v, true,
  sym := λ u v h,  trivial ,
  selfloop := λ u, trivial }

-- open_locale classical
@[symm] lemma rgraph_adj_symm {V: Type} {G: refl_graph V} {v w : V} : G.adj v w ↔ G.adj w v :=
begin
  split, intro x, exact G.sym x, intro y, exact G.sym y,
end

lemma rgraph_adj_eq_trans {V: Type} {G: refl_graph V} {v w x: V} (P: G.adj v w) (Q: w=x) : G.adj v x :=
begin
  rw Q.symm, exact P,
end

lemma rgraph_nadj_imp_neq {V: Type} {G: refl_graph V} {v w: V} (P: ¬ G.adj v w) : v ≠ w :=
begin
  classical,
  by_contradiction K,
  let P' := rgraph_adj_eq_trans (G.selfloop v) K,
  contradiction,
end

lemma rgraph_adj_cmp {V: Type} {G: refl_graph V} {v w x: V} (P: ¬ G.adj v w) (Q: G.adj v x): w ≠ x :=
begin
  classical,
  by_contradiction K,
  let P' := rgraph_adj_eq_trans Q K.symm,
  contradiction,
end

lemma rgraph_vtx_neq {V: Type} {x: V} {G: refl_graph V} (v: V) (h: ∃ (w : V), G.adj x w ∧ ¬G.adj v w) 
: some h ≠ v :=
begin
  have h': ¬G.adj v (some h),
    exact and.right (some_spec h),
  have refl: G.adj v v,
    exact G.selfloop v,
  by_contradiction C,
  have cnt: G.adj v (some h),
    exact eq.subst C.symm refl,
  contradiction,
end

lemma rgraph_vtx_neq' {V: Type} {G: refl_graph V} (v: V) (h: ∃ (w : V),  ¬G.adj v w) 
: some h ≠ v :=
begin
  have h': ¬G.adj v (some h),
    exact some_spec h,
  have refl: G.adj v v,
    exact G.selfloop v,
  by_contradiction C,
  have cnt: G.adj v (some h),
    exact eq.subst C.symm refl,
  contradiction,
end

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
(map_edges: ∀ v w, G.adj v w → H.adj (to_fun v) (to_fun w))

def graph_hom_comp {U V W : Type} {G: refl_graph U} {H: refl_graph V} {I: refl_graph W} 
  (f: graph_hom G H) (g: graph_hom H I) : graph_hom G I :=
{
  to_fun := g.to_fun ∘ f.to_fun ,
  map_edges := 
  begin
    intros u v,
    intro h,
    have adj_H : H.adj (f.to_fun u) (f.to_fun v),
      exact f.map_edges u v h,
    exact g.map_edges (f.to_fun u) (f.to_fun v) adj_H,
  end 
}

def trivial_hom {V:Type} (G: refl_graph V) : graph_hom G G :=
{
  to_fun := λ x, x,
  map_edges :=
  begin
    intros u v h, 
    exact h,
  end
}

structure graph_iso {V W: Type} (G  : refl_graph V) (H: refl_graph W) :=
(to_fun : V → W)
(bij: function.bijective to_fun)
(map_edges: ∀ v w, G.adj v w ↔ H.adj (to_fun v) (to_fun w))

def equivgraph {V W: Type} (G  : refl_graph V) (H: refl_graph W)  : Prop := nonempty(graph_iso G H)

notation G `≅` H  := equivgraph G H

def identity_iso {V: Type} (G: refl_graph V) : graph_iso G G:=
{ to_fun:= λ x,x,
  bij:= 
    begin
      unfold function.bijective,
      split, 
      { intros x y,
        intros h,
        apply h,
      },
      { intro x,
        use x,
      },
    end,
  map_edges:=
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
(cop_nocheat: ∀ K, capture K → cop_strat K = K.1)
(cop_legal: ∀ i v P, G.adj (vector.nth P i) (vector.nth (cop_strat (P,v)) i))
/-Cop doesnt sabotage himself-/

structure rob_strat {V: Type} [fintype V] (G: refl_graph V) (n : ℕ ) :=
(rob_init: vector V n → V)
(rob_strat: vector V n× V → V)
(rob_nocheat: ∀ K,  capture K → rob_strat K = K.2)
(rob_legal: ∀ v P, G.adj v (rob_strat (P,v)))

noncomputable def round {V: Type} [fintype V] {G: refl_graph V} {k : ℕ } (CS: cop_strat G k) (RS: rob_strat G k) : ℕ → vector V k × V
| 0 := (CS.cop_init, RS.rob_init (CS.cop_init))
| (n+1) := if even (n+1)
           then ((round n).1, RS.rob_strat (round n)) 
           else (CS.cop_strat (round n), (round n).2)

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

def capture_time {V: Type} [fintype V] [has_Inf ℕ] {G: refl_graph V} {n : ℕ} (CS: cop_strat G n) (RS: rob_strat G n) := Inf{k :ℕ | capture (round CS RS k)}

lemma cop_win_min_cap_time {V: Type} [fintype V] [has_Inf ℕ] {G: refl_graph V} {n : ℕ} {CS: cop_strat G n} {RS: rob_strat G n} : winning_strat_cop CS → ∃ n: ℕ, n = capture_time CS RS := begin simp, end

lemma not_cap_iff_diff_vtx {V: Type} [fintype V] {G: refl_graph V} {k : ℕ }{CS: cop_strat G k} {RS: rob_strat G k} : ∀ n : ℕ , ¬ capture (round CS RS n) ↔ ∀ i : fin k, (round CS RS n).1.nth i ≠ (round CS RS n).2 :=
begin
  intros n,
  split,
  intros h i, 
  by_contradiction K,
  have this: capture (round CS RS n),
    use i, exact K,
  contradiction, contrapose, push_neg, intro h, exact h,
end

def enum_elts (V: Type) [fintype V] [decidable_eq V]: fin (fintype.card V) ≃ V :=
(fintype.equiv_fin V).symm

lemma exists_index {V: Type} [fintype V] [decidable_eq V] (v : V)  : ∃ i, enum_elts V i = v :=
(enum_elts V).bijective.surjective v

lemma exists_index_vec {V: Type} [fintype V] [decidable_eq V] (v: V) : ∃ i, vector.nth (vector.of_fn (enum_elts V)) i = v :=
begin
  cases exists_index v with i hi, 
  use i,
  simp,
  exact hi,
end

def trivial_strategy {V: Type} [fintype V] [decidable_eq V] (G: refl_graph V) : cop_strat G (fintype.card V) :=
{
  cop_init :=  vector.of_fn (enum_elts V),
  cop_strat:= λ x, x.1,
  cop_nocheat :=
    begin
      intros K hyp,
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
      intros K hyp,
      rw capture at hyp,
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
  { let CW_strat := complete_strategy V,
    have winning : winning_strat_cop CW_strat,
    { intro RS, use 1, use 0,
      rw round, rw round, simp, refl, },
    simp, use CW_strat, exact winning, },
  have leq: Inf {k : ℕ | k_cop_win (complete_refl_graph V) k} ≤ 1,
    exact nat.Inf_le CW,
  have ge : Inf {k : ℕ | k_cop_win (complete_refl_graph V) k} >0,
    exact zero_cops_cant_win (complete_refl_graph V),
  linarith,
end

section 

variables {V: Type} [fintype V] [inhabited V] {a b: ℕ} 

def ge_cs_strat_init (va: vector V a) : vector V b :=
vector.of_fn (λ i, if h : ↑i < a then va.nth ⟨_, h⟩ else arbitrary V)

def vec_remove (va: vector V b) (ge: a ≤ b) : vector V a :=
vector.of_fn (λ i, va.nth (fin.cast_le ge i))

def ge_cs_strat_fn (strat: vector V a × V → vector V a) (ge: a ≤ b ): vector V b × V → vector V b :=
  λ x, vector.of_fn (λ i, if h : ↑i < a then (strat ⟨vec_remove x.1 ge, x.2⟩).nth ⟨_, h⟩  else x.1.nth i )

def ge_cop_strat {G: refl_graph V} (CS: cop_strat G a) (ge: a ≤ b) : cop_strat G b :=
{ cop_init := ge_cs_strat_init CS.cop_init,
  cop_strat := ge_cs_strat_fn CS.cop_strat ge,
  cop_nocheat :=
    begin
      intros K assm, 
      suffices :  ∀ (m : fin b), (ge_cs_strat_fn CS.cop_strat ge K).nth m = K.fst.nth m, exact vector.ext this,
      intro m, rw [ge_cs_strat_fn], simp, intro h, 
      let x := CS.cop_nocheat (vec_remove K.fst ge, K.snd), simp at x,
      have : (vec_remove K.fst ge).nth ⟨↑m, h⟩ =  K.fst.nth m, rw vec_remove, simp,
      rw this.symm, sorry,
    end,
  cop_legal :=
    begin
      intros i v P, rw ge_cs_strat_fn, simp, by_cases h: ¬↑i < a,
      rw dif_neg h, exact G.selfloop (P.nth i),
      simp at h, rw dif_pos h, 
      have : P.nth i = (vec_remove P ge).nth ⟨↑i, h⟩, rw vec_remove, simp, rw this,
      exact CS.cop_legal ⟨↑i, h⟩ v (vec_remove P ge),
    end }

def ge_rob_init {G: refl_graph V} (RS : rob_strat G b) : vector V a → V := λ v, RS.rob_init (ge_cs_strat_init v)

def ge_rob_fn {G: refl_graph V} (RS: rob_strat G b) : (vector V a) × V → V := 
 λ x, RS.rob_strat ⟨ge_cs_strat_init x.1, x.2⟩ 

def ge_rob_strat {G: refl_graph V} (RS: rob_strat G b) (ge: a ≤ b) : rob_strat G a := 
{ rob_init := ge_rob_init RS,
  rob_strat := ge_rob_fn RS,
  rob_legal := begin
  intros v P, rw ge_rob_fn, simp,
  exact RS.rob_legal v (ge_cs_strat_init P), end,
  rob_nocheat := begin
  intros K cap, rw ge_rob_fn, simp,
  suffices : capture (ge_cs_strat_init K.fst, K.snd), 
  exact RS.rob_nocheat (ge_cs_strat_init K.fst, K.snd) this,
  rw capture, cases cap with i cap, use fin.cast_le ge i,
  rw ge_cs_strat_init, simp, rw if_pos (fin.is_lt i), exact cap,
  end }

lemma copnumber_upwards_closed {V: Type}{G: refl_graph V}  [fintype V] [decidable_eq V] [inhabited V] : ∀ a b : ℕ, a ≤ b → a ∈ {k : ℕ | k_cop_win G k} → b ∈ {k : ℕ | k_cop_win G k} :=
begin
  intros a b ge win_a, simp, rw k_cop_win, simp at win_a, rw k_cop_win at win_a,
  cases win_a with CS win_CS, use ge_cop_strat CS ge,
  rw winning_strat_cop, rw winning_strat_cop at win_CS, intro RS, 
  specialize win_CS (ge_rob_strat RS ge), cases win_CS with n win_CS, use n,
  rw capture, cases win_CS with i win_CS, use fin.cast_le ge i, cases n,
  --zero case 
  rw round, simp, rw round at win_CS, simp at win_CS, rw ge_cop_strat, simp, 
  rw ge_cs_strat_init, simp, rw if_pos (fin.is_lt i), rw win_CS, refl,
  by_cases even(n.succ),
  --even case
  sorry, sorry,
end

end