import graphtheory
import tactic
import data.set
import data.nat.basic
import data.nat.modeq
import data.nat.parity
import logic.basic
import set_theory.zfc

open finset
open classical
open nat
open function

variables {V: Type} [fintype V] [inhabited V]

def neighbor_set (G: refl_graph V) (v : V) : set V := set_of (G.adj v)
def neighbor_set' (G: refl_graph V) (v : V) : set V := { w | G.adj v w }

lemma not_subset_iff_exists_mem_not_mem {α : Type*} {s t : set α} :
  ¬ s ⊆ t ↔ ∃ x, x ∈ s ∧ x ∉ t :=
begin
  split,
  contrapose, push_neg, intro v, exact v,
  contrapose, push_neg, intro v, exact v,
end

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

def rob_init_fn {V: Type} [fintype V] [decidable_eq V] (G: refl_graph V) : vector V 1 → V := 
 λ x, if h : ∃ w, w ≠ x.head then 
 (if g: ∃ w, ¬ G.adj x.head w then some g else some h)
 else x.head

def smart_robber {V: Type} [fintype V] [decidable_eq V] [inhabited V] (G: refl_graph V) : rob_strat G 1
:=
{ rob_init:= rob_init_fn G,
  rob_strat:= λ x , if h : ∃ w, G.adj x.2 w ∧ ¬ G.adj x.1.head w then some h else x.2,
  rob_nocheat:=
  begin
    intros K hyp,
    have hyp' : ¬∃ w, G.adj K.2 w ∧ ¬ G.adj K.1.head w,
    { by_contradiction sps,
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

--If the cop strategy is winning, the minimum round of capture is always achieved
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

--Simple lemma for reasoning
lemma cop_catch_nonempty [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V} {n: ℕ} {CS: cop_strat G n} {RS: rob_strat G n} {win : winning_strat_cop CS}{k : ℕ } (cap : k = Inf{n:ℕ | capture (round CS RS n)}) : capture (round CS RS k) ∧ ∀ i < k, ¬ capture (round CS RS i) :=
begin
  split,
  suffices this : {n_1 : ℕ | capture (round CS RS n_1)}.nonempty,
    let x := nat.Inf_mem this, rw cap.symm at x, exact x,
  rw winning_strat_cop at win, specialize win RS, cases win with w win, exact set.nonempty_of_mem win,
  intros i h, rw cap at h, exact nat.not_mem_of_lt_Inf h,
end

lemma odd_succ {n : ℕ} : odd n.succ ↔ ¬ odd n := 
by rw [succ_eq_add_one, odd_add]; simp [not_even_one]

--If the cop captures at some round n, then he captures for all m >= n
theorem capt_upwards_closed [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V} {n: ℕ} {CS: cop_strat G n} {RS: rob_strat G n} : ∀ k1 k2 : ℕ , k1 ≤ k2 → k1 ∈ {n:ℕ | capture (round CS RS n)} → k2 ∈ {n:ℕ | capture (round CS RS n)} :=
begin
  intros k1 k2 le inc,
  suffices : ∀ k1, k1 ∈ {n:ℕ | capture (round CS RS n)} → k1.succ ∈ {n:ℕ | capture (round CS RS n)},
  { exact nat.le_rec_on le this inc,},
  intros k1 hyp,
  simp at hyp, clear inc, simp, 
  cases k1, unfold capture, unfold round, simp, 
  let nocheat := CS.cop_nocheat (round CS RS 0) hyp,
  rw [capture, round] at hyp, cases hyp with m hyp, simp at hyp,
  use m, conv {
  to_rhs, rw hyp.symm,  
  }, unfold round at nocheat, rw nocheat,
  cases (nat.even_or_odd k1_1.succ), 
  rw [nat.even_iff_not_odd, odd_succ.symm, nat.odd_iff_not_even, nat.even_iff] at h,
  let nocheat := CS.cop_nocheat (round CS RS k1_1.succ) hyp,
  rw capture at hyp, cases hyp with m hyp, use m,
  rw [(nat.one_add k1_1.succ).symm, nat.add_comm] at h, rw round, rw if_neg h, clear h, simp, rw [nocheat, hyp],
  rw [nat.odd_iff_not_even, nat.even_succ.symm, nat.even_iff] at h,
  let nocheat := RS.rob_nocheat (round CS RS k1_1.succ) hyp,
  rw capture at hyp, cases hyp with m hyp, use m,
  rw [(nat.one_add k1_1.succ).symm, nat.add_comm] at h, rw round, rw if_pos h, clear h, simp, rw [nocheat, hyp],
end

lemma or_iff_right {a b : Prop} (ha : ¬ a) : a ∨ b ↔ b := ⟨λ h, h.resolve_left ha, or.inr⟩

lemma mod2_zero_or_one : ∀ n : ℕ, n%2=1 ∨ n%2=0 :=
begin
  intro n,
  rw nat.even_iff.symm, rw nat.odd_iff.symm,
  exact (nat.even_or_odd n).symm,
end

lemma even_succ_succ : ∀ n : ℕ, even n.succ.succ ↔ even n :=
begin
  intro n, 
  rw [nat.even_succ, nat.odd_iff_not_even.symm, odd_succ, nat.even_iff_not_odd.symm],
end

lemma odd_succ_succ : ∀ n : ℕ, odd n.succ.succ ↔ odd n :=
begin
  intro n, 
  rw [odd_succ, nat.even_iff_not_odd.symm, nat.even_succ, nat.odd_iff_not_even.symm],
end

-- A smart robber will never get caught on their own turn
theorem smart_capture_cop_move [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V} {CS: cop_strat G 1} {n : ℕ} (p: winning_strat_cop CS) (cap : n = Inf{n:ℕ | capture (round CS (smart_robber G) n)}) (gt: n > 0) : n%2=1 :=
begin
  rw winning_strat_cop at p, specialize p (smart_robber G), 
  have non: {n:ℕ | capture (round CS (smart_robber G) n)}.nonempty,
    rw set.nonempty_def, simp, exact p,
  by_contradiction K, 
  have K': n%2=0,
    exact (or_iff_right K).1 (mod2_zero_or_one n),
  have pred_no_cap: ∀ m < n, ¬ capture (round CS (smart_robber G) m),
    intros m h, rw cap at h, exact nat.not_mem_of_lt_Inf h,
  have cap' : capture (round CS (smart_robber G) n),
    let x := nat.Inf_mem non, rw cap.symm at x, exact x,
  clear cap,
  specialize pred_no_cap n.pred,
  have this : n.pred < n,
    suffices this :n ≠ 0, exact nat.pred_lt this, linarith,
  specialize pred_no_cap this, clear this,
  suffices goal : (round CS (smart_robber G) n).1.head ≠ (round CS (smart_robber G) n).2,
    have nocap_atn : ¬ capture (round CS (smart_robber G) n),
      rw capture, push_neg, intro i, have this: i=0, simp, rw this, simp, exact goal,
    contradiction,
  have rob_in_place: (smart_robber G).rob_strat (round CS (smart_robber G) n.pred) = (round CS (smart_robber G) n.pred).2,
    cases n, contradiction, rw (nat.pred_succ n),
    suffices this: ¬ (∃ (w : V), G.adj (round CS (smart_robber G) n).snd w ∧ ¬G.adj (round CS (smart_robber G) n).fst.head w),
      conv {
        to_lhs, congr, rw smart_robber, --command 'skip' to get 3rd rw 
      }, simp, rw dif_neg this, clear K,
    by_contradiction K, 
    have contradiction: ¬ capture (round CS (smart_robber G) n.succ),
      have this : (smart_robber G).rob_strat (round CS (smart_robber G) n) = some K,
        conv {
          to_lhs, congr, rw smart_robber, 
        }, simp, rw dif_pos K,
      rw capture, push_neg, intro i, have this: i=0, simp, rw this, clear this, clear i, simp,
      unfold round, rw (nat.add_one n).symm at K', rw if_pos K', simp, rw this, clear this,
      suffices this: ¬G.adj (round CS (smart_robber G) n).fst.head (some K),
        exact rgraph_nadj_imp_neq this,
      exact and.elim_right (classical.some_spec K),
    contradiction,
  unfold capture at cap', unfold capture at pred_no_cap, push_neg at pred_no_cap,
  specialize pred_no_cap 0,
  cases cap' with i cap', have this: i=0, simp, rw this at cap', clear this, clear i,
  cases n, contradiction,
  rw round, rw (nat.add_one n).symm at K', rewrite if_pos K', simp,
  rw (nat.pred_succ n) at rob_in_place, rw (nat.pred_succ n) at pred_no_cap, 
  simp at pred_no_cap, rw rob_in_place.symm at pred_no_cap, exact pred_no_cap, 
end

--A smart robber will stay in place before cop captures.
theorem smart_rob_in_place [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V} {CS: cop_strat G 1} {n : ℕ} (p: winning_strat_cop CS) (cap : n = Inf{n:ℕ | capture (round CS (smart_robber G) n)}) (gt: n > 1) : (round CS (smart_robber G) n.pred.pred).2  = (round CS (smart_robber G) n.pred).2 :=
begin
 cases n, let x := nat.not_lt_zero 1, contradiction,
 cases n, let x := nat.lt_irrefl 1, contradiction,
 rw nat.pred_succ (n.succ), rw nat.pred_succ n, 
 let cap' := and.left (cop_catch_nonempty cap), 
 cases (nat.even_or_odd n.succ.succ),
 rw [nat.even_succ, nat.even_iff, nat.succ_eq_add_one] at h, 
 conv { to_rhs, rw round, }, rw if_neg h,
 rw [odd_succ, nat.odd_iff_not_even, nat.succ_eq_add_one, nat.even_iff] at h, push_neg at h, 
 conv { to_rhs, rw round, }, rw if_pos h, simp, 
 conv { to_rhs, congr,rw smart_robber, }, simp,
 suffices this : ¬ ∃ (w : V), G.adj (round CS (smart_robber G) n).snd w ∧ ¬G.adj (round CS (smart_robber G) n).fst.head w,
  rw dif_neg this,
 by_contradiction K,
 have this: ¬ capture (round CS (smart_robber G) n.succ.succ),
  have this : (smart_robber G).rob_strat (round CS (smart_robber G) n) = some K,
    conv {
      to_lhs, congr, rw smart_robber, 
    }, simp, rw dif_pos K,
  rw capture, push_neg, intro i, have this: i=0, simp, rw this, clear this, clear i, simp, 
  rw round, have this : ¬(n.succ + 1) % 2 = 0, rw [(nat.succ_eq_add_one n.succ).symm, nat.even_iff.symm, nat.odd_iff_not_even.symm], rw [nat.even_iff.symm,(nat.succ_eq_add_one n).symm, nat.even_iff_not_odd] at h, 
  exact odd_succ.2 h,
  rw if_neg this, simp,
 contradiction,
 exact p,
end

lemma if_one_mod2_not_zero (n : ℕ ) : n%2 = 1 → ¬ (n % 2 = 0) :=
begin
  intro h, linarith,
end

lemma if_succ_one_mod2_zero {n : ℕ } : n.succ%2 = 1 → n % 2 = 0 :=
begin
  intro h, rw nat.odd_iff.symm at h,
  have this: odd n.succ → even n,
    contrapose, rw (nat.even_iff_not_odd).symm, exact nat.even_succ.2,
  exact nat.even_iff.1 (this h),
end

theorem cwg_has_corner [complete_semilattice_Inf ℕ] [fintype V] [decidable_eq V] [inhabited V] (G: refl_graph V): 
cop_win_graph G → has_corner G := 
begin
  intro CW,
  rw [cop_win_graph,cop_number] at CW,
  have cop_win: k_cop_win G 1,
  {
    have non: {k : ℕ | k_cop_win G k}.nonempty,
    exact lots_of_cops G,
    let E:= nat.Inf_mem non,
    rw CW at E,
    apply E,
  },
  cases cop_win with CS h,
  rw has_corner,
  let RS := smart_robber G,
  have min : ∃ n:ℕ , n = Inf{n:ℕ | capture (round CS RS n)},
    apply wcs_min_rounds CS h,
  cases min with w hw,
  cases w with w wsucc,
  {
    apply or.inl,
    have cap : capture (round CS RS 0),
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
      exact zero_in,
    rw [capture, round] at cap, simp at cap,
    cases cap with i cap, have this: i=0, simp, rw this at cap,
    have: ∀ w, w= CS.cop_init.head,
    { by_contradiction K,
      push_neg at K,
      change _ = (smart_robber G).rob_init _ at cap,
      have x : rob_init_fn G CS.cop_init ≠ CS.cop_init.head,
      { unfold rob_init_fn,
        rw dif_pos K, 
        by_cases h: ∃ (w : V), ¬G.adj CS.cop_init.head w,
        { rw dif_pos h,
          exact rgraph_vtx_neq' CS.cop_init.head h,
        },
        rw dif_neg h, push_neg at h,
        exact some_spec K,
      },
      have y : (smart_robber G).rob_init CS.cop_init ≠ rob_init_fn G CS.cop_init,
        simp at cap,
        exact ne_of_eq_of_ne cap.symm x.symm,
      contradiction,
    },
    exact fintype.card_eq_one_of_forall_eq this,
  },
  apply or.inr,
  have cap : capture (round CS RS w.succ),
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
  have w_succ_odd: w.succ%2=1,
    have this: w.succ>0,
      exact nat.succ_pos',
    exact smart_capture_cop_move h hw this,
  rw [capture, round] at cap, cases cap with i cap, 
  have this: i=0, simp, rw this at cap, clear this, clear i, simp at cap, 
  rw if_neg ((if_one_mod2_not_zero w.succ) w_succ_odd) at cap, simp at cap,
  unfold corner_vtx,
  by_contradiction K,
  push_neg at K, 
  have beforeCap : (round CS RS w).1.head ≠ (round CS RS w).2,
    by_contradiction, simp at h,
    have this: capture (round CS RS w),
      unfold capture, use 0,  simp, exact h,
    have contradiction : Inf {n : ℕ | capture (round CS RS n)} ≤ w,
      have that: w ∈ {n : ℕ | capture (round CS RS n)},
        simp, exact this,
      exact nat.Inf_le this,
    rw hw.symm at contradiction, exact nat.lt_asymm contradiction contradiction,
  specialize K (round CS RS w).2 (round CS RS w).1.head beforeCap,
  rw not_subset_iff_exists_mem_not_mem at K,
  unfold neighbor_set' at K, simp at K,
  have this : ¬ capture (round CS RS w.succ),
    rw [capture, round], simp, intro x, 
    have this : x=0, simp, rw this, clear this, clear x,
    rw if_neg ((if_one_mod2_not_zero w.succ) w_succ_odd), simp,
    have this : w % 2 = 0, exact if_succ_one_mod2_zero w_succ_odd,
    sorry, --Need some way to argue about the predecessor of w
  have that : capture (round CS RS w.succ),
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
  contradiction,
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
  cop_strat := λ x, vector.map (F.f).to_fun (CS.cop_strat (x.1.map subtype.val,x.2.val)),
  cop_nocheat := sorry
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
  sorry,
end


