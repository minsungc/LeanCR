import graphtheory

open finset
open classical

variables {V: Type} [fintype V]

def neighbor_set (G: refl_graph V) (v : V) : set V := set_of (G.adj v)
def neighbor_set' (G: refl_graph V) (v : V) : set V := { w | G.adj v w }

/-
Corner vertices, an important concept in Cops and Robbers
A vtx w is a corner iff there exists some vertex v such that the neighbors of w is a subset of the neighbors of v
-/

def corner_vtx (G: refl_graph V) (w: V)  : Prop :=
  (∃ v , v ≠ w ∧ (neighbor_set G w) ⊆ (neighbor_set G v))

def has_corner (G: refl_graph V) : Prop :=
  (∃ w , corner_vtx G w)

open_locale classical
noncomputable theory 

def rob_init_fn {V: Type} [fintype V] [decidable_eq V] (G: refl_graph V) : vector V 1 → V := 
 λ x, if h : ∃ w, ¬ G.adj x.head w then some h else x.head

def rob_strat_fn {V: Type} [fintype V] [decidable_eq V] (G: refl_graph V) : vector V 1 × V → V :=
  λ x , if h : ∃ w, G.adj x.2 w ∧ ¬ G.adj x.1.head w then some h else x.2

theorem rsfn_works [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V}
    (P : vector V 1 × V)  (h : ∃ w, G.adj P.2 w ∧ ¬ G.adj P.1.head w) :
  G.adj P.2 (rob_strat_fn G P) ∧ ¬ G.adj P.1.head (rob_strat_fn G P) :=
begin
  rewrite rob_strat_fn,
  simp,
  rw dif_pos h,
  apply some_spec h,
end

theorem rsfn_works' [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V}
     (P : vector V 1 × V) (h : ¬ ∃ w, G.adj P.2 w ∧ ¬ G.adj P.1.head w) :
  rob_strat_fn G P = P.2 :=
begin
  rewrite rob_strat_fn,
  simp,
  rw dif_neg h,
end

lemma adj [fintype V] [decidable_eq V] [inhabited V] (G: refl_graph V) (P : vector V 1 × V) :
  G.adj P.2 (rob_strat_fn G P) :=
begin
  by_cases h : ∃ w, G.adj P.2 w ∧ ¬ G.adj P.1.head w,
  { exact (rsfn_works P h).1 },
  rw rsfn_works' P h,
  apply G.selfloop,
end

def smart_robber {V: Type} [fintype V] [decidable_eq V] [inhabited V] (G: refl_graph V) : rob_strat G 1
:=
{
  rob_init:= rob_init_fn G,
  rob_strat:= rob_strat_fn G,
  rob_nocheat:=
  begin
    intros K hyp,
    rw rob_strat_fn,
    have hyp' : ¬∃ w, G.adj K.2 w ∧ ¬ G.adj K.1.head w,
    {
      by_contradiction sps,
      rw capture at hyp,
      cases hyp with w hw,
      have this: w=0,
        simp,
      rw this at hw,
      simp at hw,
      rw hw at sps,
      cases sps with y hy,
      exact (and_not_self (G.adj K.snd y)).mp hy,
    },
    simp,
    rw dif_neg hyp',
  end,
  rob_legal:= 
  begin
    intros v P,
    let J := (P,v),
    exact adj G J,
  end,
}

theorem wcs_min_rounds [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V} {k :ℕ }  
  (CS: cop_strat G k) :
  winning_strat_cop CS → ∀ RS: rob_strat G k, ∃ n:ℕ , n = Inf{n:ℕ | capture (round CS RS n)} :=
begin
  intro h,
  intro RS,
  rw winning_strat_cop at h,
  specialize h RS,
  simp,
end

theorem cwg_has_corner [fintype V] [decidable_eq V] [inhabited V] (G: refl_graph V): 
cop_win_graph G → has_corner G := 
begin
  intro CW,
  rw cop_win_graph at CW,
  rw cop_number at CW,
  have non: {k : ℕ | k_cop_win G k}.nonempty,
    exact lots_of_cops G,
  have cop_win: k_cop_win G 1,
  {
    let E:= nat.Inf_mem non,
    rw CW at E,
    apply E,
  },
  rw k_cop_win at cop_win,
  rwa has_corner,
  cases cop_win with CS h,
  let RS := smart_robber G,
  have min : ∃ n:ℕ , n = Inf{n:ℕ | capture (round CS RS n)},
    apply wcs_min_rounds CS h,
  cases min with w hw,
  have w_cap : capture (round CS RS w),
  {
    have ne: {n : ℕ | capture (round CS RS n)}.nonempty,
    {
      unfold winning_strat_cop at h,
      specialize h RS,
      rwa set.nonempty_def,     
    },
    have w_in: w ∈ {n : ℕ | capture (round CS RS n)},
    {
      have this: Inf{n : ℕ | capture (round CS RS n)} ∈ {n : ℕ | capture (round CS RS n)},
        exact nat.Inf_mem ne,
      rw hw.symm at this,
      exact this,
    },
    exact w_in,
  },
  use (round CS RS (w-1)).2,
  rw corner_vtx,
  use (round CS RS (w-1)).1.head,
  split,
  { 
    by_contradiction sps,
    simp at sps,
    have uhoh : capture (round CS RS (w-1)),
    {
      rw capture,
      use 0,
      simp, exact sps,
    },
    have uhoh' : w-1 ∈ {n : ℕ | capture (round CS RS n)} ,
      exact uhoh,
    have uhoh'' : Inf {n : ℕ | capture (round CS RS n)} ≤ w-1 ,
      apply nat.Inf_le uhoh',
    rw hw.symm at uhoh'',
    have con1 : w+1 ≤ w,
      sorry,
    have con2 : ¬ w+1 ≤ w,
      exact nat.not_succ_le_self w,
    contradiction,
  },
  intros v hv,
  unfold capture at w_cap,
  cases w_cap with zero h_zero,
  have this: zero=0,
    simp,
  rw this at h_zero,
  have rob_in_place: (round CS RS (w - 1)).snd = (round CS RS w).snd,
  {
    rw h_zero.symm,
    simp,
    let prev:= round CS RS (w-1),
    have a: (round CS RS w).fst = CS.cop_strat prev,
    {
      rw round,
    }
  }
  -- have capture: capture (CS.cop_strat (round CS RS (w - 1)), (round CS RS (w - 1)).snd),
  -- {
  --   rw capture,
  --   use 0,
  --   simp,
  -- },
  
end



def induced_subgraph (S: fintype V) (G: refl_graph V) : refl_graph {v:V//v ∉ S.elems} :=
{ adj := λ a b, G.adj a b, 
  sym :=  λ a b h, G.sym h,
  selfloop := 
  begin
    intro a, 
    apply G.selfloop,
  end  
}

def retract {c: V} (G: refl_graph V) (H:= induced_subgraph {c} G)  := 
  ∃ f: graph_hom G H, ∀ v ≠ c, v = f.to_fun(v)

def dismantle (G: refl_graph V) : list V → Prop
| [] := G ≅ singleton_graph 
| (a::L) := (corner_vtx G a) ∧ dismantle L

def dismantlable_graph (G: refl_graph V) := ∃ L, dismantle G L

lemma cop_num_le_retract {c:V} (G: refl_graph V) (H:= induced_subgraph {c} G) : 
retract G H → cop_number H ≤ cop_number G :=


