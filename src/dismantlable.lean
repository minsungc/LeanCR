import graphtheory
import data.fintype.basic

open finset
open classical


variables {V: Type} [fintype V] [inhabited V]

def neighbor_set (G: refl_graph V) (v : V) : set V := set_of (G.adj v)
def neighbor_set' (G: refl_graph V) (v : V) : set V := { w | G.adj v w }

/-
Corner vertices, an important concept in Cops and Robbers
A vtx w is a corner iff there exists some vertex v such that the neighbors of w is a subset of the neighbors of v
-/

def corner_vtx (G: refl_graph V) (w: V)  : Prop :=
  (∃ v , v ≠ w ∧ (neighbor_set' G w) ⊆ (neighbor_set' G v))

def has_corner [inhabited V] (G: refl_graph V) : Prop :=
  fintype.card V=1 ∨ (∃ w , corner_vtx G w)

def corner_cmp (G: refl_graph V) (v w: V)  : Prop :=
  v ≠ w ∧ (neighbor_set' G w) ⊆ (neighbor_set' G v)

open_locale classical
noncomputable theory 
 

def rob_init_fn {V: Type} [fintype V] [decidable_eq V] (G: refl_graph V) : vector V 1 → V := 
 λ x, if h : ∃ w, x.head ≠  w then 
 (if g: ∃ w, ¬ G.adj x.head w then some g else some h)
 else x.head

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
  rob_strat:= λ x , if h : ∃ w, G.adj x.2 w ∧ ¬ G.adj x.1.head w then some h else x.2,
  rob_nocheat:=
  begin
    intros K hyp,
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

lemma inits [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V}
  (CS: cop_strat G 1) (cap: capture (round CS (smart_robber G) 0))
  :  ((smart_robber G).rob_init CS.cop_init= CS.cop_init.head ) :=
  begin
    rw capture at cap,
    cases cap with i hi,
    have this: i=0,
      simp,
    rw this at hi,
    simp at hi,
    exact hi.symm,
  end

theorem initial_catch [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V}
  (CS: cop_strat G 1) 
  : capture (round CS (smart_robber G) 0) → ∀ w, CS.cop_init.head = w :=
begin
  intros cap, 
  let RS:= smart_robber G,
  have same : (smart_robber G).rob_init CS.cop_init=CS.cop_init.head ,
    exact inits CS cap,
  have neq: ¬∃ w, CS.cop_init.head ≠ w,
  { push_neg,
    sorry,
  },
  simp at neq,
  exact neq,
end

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

#check eq.symm
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
  cases w with w wsucc,
  { 
    have zero_in : 0 ∈ {n : ℕ | capture (round CS RS n)},
    { have zero_or : 0 ∈ {n : ℕ | capture (round CS RS n)} ∨ {n : ℕ | capture (round CS RS n)} = ∅,
        apply nat.Inf_eq_zero.1 hw.symm,
      have zero_nonempty: {n : ℕ | capture (round CS RS n)}.nonempty,
      { rw winning_strat_cop at h,
        specialize h RS,
        cases h with n hn,
        use n,
        exact hn,
      },
      apply or.resolve_right zero_or,
      exact set.nonempty.ne_empty zero_nonempty,
    },
    simp at zero_in,
    rw [capture,round] at zero_in,
    cases zero_in with i hi,
    have this: i=0,
        simp,
    rw this at hi,
    simp at hi,
    apply or.inl,
    suffices : V ≃ unit,
      exact eq.trans (fintype.card_congr this) fintype.card_unit,
    suffices : fintype.card V = 1,
      exact fintype.equiv_of_card_eq (eq.trans this (fintype.card_unit).symm),
    have this: ∀ w, w= CS.cop_init.head,
    { 
      
    },
    exact fintype.card_eq_one_of_forall_eq this,
  },
  have w_cap : capture (round CS RS w.succ),
  {
    have ne: {n : ℕ | capture (round CS RS n)}.nonempty,
    {
      unfold winning_strat_cop at h,
      specialize h RS,
      rwa set.nonempty_def,     
    },
    have w_in: w.succ ∈ {n : ℕ | capture (round CS RS n)},
    {
      have this: Inf{n : ℕ | capture (round CS RS n)} ∈ {n : ℕ | capture (round CS RS n)},
        exact nat.Inf_mem ne,
      rw hw.symm at this,
      exact this,
    },
    exact w_in,
  },
  apply or.inr,
  use (round CS RS w).2,
  rw corner_vtx,
  use (round CS RS w).1.head,
  split,
  { 
    by_contradiction sps,
    simp at sps,
    have uhoh : capture (round CS RS w),
    {
      rw capture,
      use 0,
      simp, exact sps,
    },
    have uhoh' : w ∈ {n : ℕ | capture (round CS RS n)} ,
      exact uhoh,
    have uhoh'' : Inf {n : ℕ | capture (round CS RS n)} ≤ w ,
      apply nat.Inf_le uhoh',
    rw hw.symm at uhoh'',
    have contra: ¬ w.succ ≤ w,
      exact nat.not_succ_le_self w,
    contradiction,
  },
  intros v hv,
  rw neighbor_set' at hv,
  simp at hv,
  unfold capture at w_cap,
  cases w_cap with i hi,
  have this: i=0,
    simp,
  rw this at hi,
  rw neighbor_set',
  simp,
  simp at hi,
  have rob_in_place: (round CS RS w).snd = (round CS RS w.succ).snd,
  { 
    have capt: capture (CS.cop_strat (round CS RS w), (round CS RS w).snd),
    {
      rw capture,
      use 0,
      simp,
    }
  }
  -- have capture: capture (CS.cop_strat (round CS RS (w - 1)), (round CS RS (w - 1)).snd),
  -- -- {
  -- --  
  -- -- },
  
end



def induced_subgraph (S: set V) (G: refl_graph V) : refl_graph {v:V// v ∈ S} :=
{ adj := λ a b, G.adj a b, 
  sym :=  λ a b h, G.sym h,
  selfloop := 
  begin
    intro a, 
    apply G.selfloop,
  end  
}


structure retract {c: V} (G: refl_graph V) (H:= induced_subgraph {v: V | v ≠ c} G)  := 
  (f: graph_hom G H)
  (id: ∀ v ≠ c, v = f.to_fun(v))
  (corner: corner_cmp G c ↑(f.to_fun(c)))

def dismantle (G: refl_graph V) : list V → Prop
| [] := G ≅ singleton_graph 
| (a::L) := (corner_vtx G a) ∧ dismantle L

def dismantlable_graph (G: refl_graph V) := ∃ L, dismantle G L


def image_strat {V: Type} [fintype V] [decidable_eq V] [inhabited V] {c:V} {n: ℕ }
(G: refl_graph V) (H := induced_subgraph  {v: V | v ≠ c} G) (F: retract G H)
(CS: cop_strat G n)
: cop_strat H n :=
{
  cop_init := vector.map (F.f).to_fun CS.cop_init,
  cop_strat := λ x, vector.map (F.f).to_fun (CS.cop_strat ↑x),
  cop_nocheat :=
  begin
      
  end
}

lemma cop_num_le_retract {V: Type} [fintype V] [decidable_eq V] [inhabited V] {c:V} (G: refl_graph V) (H := induced_subgraph {v: V | v ≠ c} G) : 
retract G H → cop_number H ≤ cop_number G :=
begin
  intro hyp,
  cases hyp with f id corner,
  unfold cop_number,
  let n:= Inf {k : ℕ | k_cop_win G k},
  suffices : k_cop_win H n,
    exact nat.Inf_le this,
  have n_win: k_cop_win G n,
    exact nat.Inf_mem (lots_of_cops G), 
  rw k_cop_win at n_win,
  cases n_win with CS hCS,
  let CS' := cop_strat H n,

end


