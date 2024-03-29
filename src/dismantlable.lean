import graphtheory
import tactic
import data.set
import data.nat.basic
import data.nat.modeq
import data.nat.parity
import data.nat.lattice
import logic.basic
import set_theory.zfc

open finset
open classical
open nat
open function

variables {V: Type} [fintype V] [inhabited V] [decidable_eq V]

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
noncomputable theory 

def corner_vtx (G: refl_graph V) (w: V)  : Prop :=
  (∃ (v: V) (h: v ≠ w), (neighbor_set' G w) ⊆ (neighbor_set' G v))

def cornering_vtx (G: refl_graph V) (w: V) (h: corner_vtx G w) : V := some h

def has_corner (G: refl_graph V) : Prop :=
  fintype.card V=1 ∨ (∃ w , corner_vtx G w)

def corner_cmp (G: refl_graph V) (v w: V)  : Prop :=
  v ≠ w ∧ (neighbor_set' G w) ⊆ (neighbor_set' G v)

open_locale classical
noncomputable theory 

lemma odd_succ {n : ℕ} : odd n.succ ↔ ¬ odd n := 
by rw [succ_eq_add_one, odd_add]; simp [not_even_one]

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

def rob_strat_fn (G: refl_graph V) : vector V 1 × V → V :=
  λ x , if h : ∃ w, G.adj x.2 w ∧ ¬ G.adj x.1.head w then some h else x.2

theorem rsfn_works {G: refl_graph V}
    (P : vector V 1 × V)  (h : ∃ w, G.adj P.2 w ∧ ¬ G.adj P.1.head w) :
  G.adj P.2 (rob_strat_fn G P) ∧ ¬ G.adj P.1.head (rob_strat_fn G P) :=
begin
  rewrite rob_strat_fn,
  simp,
  rw dif_pos h,
  apply some_spec h,
end

theorem rsfn_works' {G: refl_graph V}
     (P : vector V 1 × V) (h : ¬ ∃ w, G.adj P.2 w ∧ ¬ G.adj P.1.head w) :
  rob_strat_fn G P = P.2 :=
begin
  rw rob_strat_fn, simp, by_contradiction K, simp at K, cases K with x K,cases K with h' K,
  push_neg at h, specialize h x, specialize h h'.1, have h'' : ¬G.adj P.fst.head x, exact h'.2, 
  contradiction,
end

lemma adj (G: refl_graph V) (P : vector V 1 × V) :
  G.adj P.2 (rob_strat_fn G P) :=
begin
  by_cases h : ∃ w, G.adj P.2 w ∧ ¬ G.adj P.1.head w,
  { exact (rsfn_works P h).1 },
  rw rsfn_works' P h,
  apply G.selfloop,
end

def rob_init_fn  (G: refl_graph V) : vector V 1 → V := 
 λ x, if h : ∃ w, w ≠ x.head then 
 (if g: ∃ w, ¬ G.adj x.head w then some g else some h)
 else x.head

def pre_smart_robber (G: refl_graph V) : pre_rob_strat G 1 :=
{ init := rob_init_fn G, strat := rob_strat_fn G }

def smart_robber (G: refl_graph V) : rob_strat G 1
:=
{ strat := pre_smart_robber G,
  nocheat:=
  begin
    intros CS i cap, conv {congr, congr, rw pre_smart_robber}, simp,
    set K := (pre_round CS (pre_smart_robber G) i),
    have hyp' : ¬∃ w, G.adj K.2 w ∧ ¬ G.adj K.1.head w,
    { by_contradiction sps,
      cases cap with w hw, have this: w=0, simp, rw this at hw, simp at hw,
      rw hw at sps, cases sps with y hy, exact (and_not_self (G.adj K.snd y)).mp hy, },
    rw rob_strat_fn, simp, 
    by_contradiction K', push_neg at K', cases K' with x K', cases K' with h' K',
    push_neg at hyp', specialize hyp' x, specialize hyp' h'.1, have h'' : ¬G.adj K.fst.head x, exact h'.2, 
    contradiction,
  end,
  legal:= begin intros v P, exact adj G (P, v), end,
}

--If the cop strategy is winning, the minimum round of capture is always achieved
theorem wcs_min_rounds {G: refl_graph V} {k :ℕ }  
  (CS: cop_strat G k) :
  winning_strat_cop CS → ∀ RS: rob_strat G k, ∃ n:ℕ , n = Inf{n:ℕ | capture (round CS RS n)} :=
begin
  intro h, intro RS, rw winning_strat_cop at h, specialize h RS, simp,
end

--If the cop captures at some round n, then he captures for all m >= n
theorem capt_upwards_closed {G: refl_graph V} {n: ℕ} {CS: cop_strat G n} {RS: rob_strat G n} : ∀ k1 k2 : ℕ , k1 ≤ k2 → k1 ∈ {n:ℕ | capture (round CS RS n)} → k2 ∈ {n:ℕ | capture (round CS RS n)} :=
begin
  intros k1 k2 le inc,
  suffices : ∀ k1, k1 ∈ {n:ℕ | capture (round CS RS n)} → k1.succ ∈ {n:ℕ | capture (round CS RS n)}, { exact nat.le_rec_on le this inc,}, clear inc le k1 k2,
  intros k1 hyp, simp at hyp, simp, 
  cases k1, rw [capture, round], simp,
  let nocheat := CS.nocheat RS.strat 0 hyp,
  rw round at hyp, rw capture at hyp, cases hyp with m hyp', rw pre_round at hyp', simp at hyp',
  use m, rw [pre_round, hyp'.symm] at nocheat, rw pre_round, simp, rw pre_round, simp, rw hyp'.symm, rw nocheat,
  cases (nat.even_or_odd k1.succ), 
  rw [nat.even_iff_not_odd, odd_succ.symm, nat.odd_iff_not_even] at h,
  let nocheat := CS.nocheat RS.strat k1.succ hyp,
  cases hyp with m hyp, use m, rw [round, pre_round, if_neg h, nocheat], simp, rw round at hyp, exact hyp, 
  rw [nat.odd_iff_not_even, nat.even_succ.symm] at h,
  let nocheat := RS.nocheat CS.strat k1.succ hyp,
  cases hyp with m hyp, use m, rw [round, pre_round, if_pos h, nocheat], rw round at hyp, exact hyp,
end

--Simple lemma for reasoning
lemma cop_catch_nonempty {G: refl_graph V} {n: ℕ} {CS: cop_strat G n} {RS: rob_strat G n} {win : winning_strat_cop CS} {k : ℕ } : k = Inf{n:ℕ | capture (round CS RS n)} ↔ capture (round CS RS k) ∧ ∀ i < k, ¬ capture (round CS RS i) :=
begin
  split, intro cap, split,
  suffices this : {n_1 : ℕ | capture (round CS RS n_1)}.nonempty,
    let x := nat.Inf_mem this, rw cap.symm at x, exact x,
  specialize win RS, cases win with w win, exact set.nonempty_of_mem win,
  intros i h, rw cap at h, exact nat.not_mem_of_lt_Inf h,
  intro h, cases k, symmetry, rw nat.Inf_eq_zero, exact or.inl h.1,
  symmetry, rw nat.Inf_upward_closed_eq_succ_iff, split, exact h.1, 
  simp, exact h.2 k (nat.lt_succ_self k), exact capt_upwards_closed,
end

--A smart robber will stay in place before cop captures.
theorem smart_rob_in_place {G: refl_graph V} {CS: cop_strat G 1} {n : ℕ} (p: winning_strat_cop CS) (cap : n = Inf{n:ℕ | capture (round CS (smart_robber G) n)}) (gt: n > 1) : (round CS (smart_robber G) n.pred.pred).2  = (round CS (smart_robber G) n.pred).2 :=
begin
 cases n, let x := nat.not_lt_zero 1, contradiction,
 cases n, let x := nat.lt_irrefl 1, contradiction,
 rw [nat.pred_succ (n.succ), nat.pred_succ n], 
 rw cop_catch_nonempty at cap,
 cases (nat.even_or_odd n.succ.succ),
 -- if n+2 is even
 rw nat.even_succ at h, 
 conv { to_rhs, rw round, rw pre_round}, rw if_neg h, rw round,
-- if n+2 is odd
 rw [odd_succ, nat.odd_iff_not_even, nat.succ_eq_add_one] at h, push_neg at h, 
 conv { to_rhs, rw round, rw pre_round}, rw if_pos h, simp, 
 conv { to_rhs, congr,rw smart_robber, }, simp,
 suffices this : ¬ ∃ (w : V), G.adj (round CS (smart_robber G) n).snd w ∧ ¬G.adj (round CS (smart_robber G) n).fst.head w,
  rw pre_smart_robber, simp, rw rob_strat_fn, simp, rw round at this, rw dif_neg this, refl,
 by_contradiction K,
 have this: ¬ capture (round CS (smart_robber G) n.succ.succ),
  rw capture, push_neg, intro i, have this: i=0, simp, rw this, clear this i, simp, 
  rw round, have this : ¬ even (n.succ +1), simp with parity_simps, exact nat.even_succ.1 h,
  rw [pre_round, if_neg this, pre_round, if_pos h], simp, conv { congr, to_rhs, congr, rw smart_robber,}, simp, rw [pre_smart_robber, rob_strat_fn], simp, rw round at K, rw dif_pos K,
  have nadj1 : ¬ G.adj (round CS (smart_robber G) n).fst.head (some K), by exact (some_spec K).2,
  have nadj2: G.adj ((round CS (smart_robber G) n).1.head) ((CS.strat.strat (round CS (smart_robber G) n.succ)).head),
    conv{ congr, skip, skip, rw [round, pre_round]}, rw if_pos h,
    let x := CS.legal 0 ((smart_robber G).strat.strat (round CS (smart_robber G) n)) (round CS (smart_robber G) n).1,
    simp at x, exact x,
  let x := (rgraph_adj_cmp nadj1 nadj2).symm, rw [round, pre_round, if_pos h] at x, exact x,
 exact this (cap.1), exact p,
end

-- A smart robber will never get caught on their own turn
theorem smart_capture_cop_move {G: refl_graph V} {CS: cop_strat G 1} {n : ℕ} (p: winning_strat_cop CS) (cap : n = Inf{n:ℕ | capture (round CS (smart_robber G) n)}) (gt: n > 0) : odd n :=
begin
  rw cop_catch_nonempty at cap,
  have : n ≠ 0, linarith,
  let pred_no_cap := cap.2 n.pred (nat.pred_lt this),
  by_contradiction,
  suffices goal : (round CS (smart_robber G) n).1.head ≠ (round CS (smart_robber G) n).2,
    have nocap_atn : ¬ capture (round CS (smart_robber G) n),
      rw capture, push_neg, intro i, have this: i=0, simp, rw this, simp, exact goal,
    exact nocap_atn cap.1,
  have rob_in_place: (smart_robber G).strat.strat (round CS (smart_robber G) n.pred) = (round CS (smart_robber G) n.pred).2,
    cases n, contradiction, rw (nat.pred_succ n),
    suffices this: ¬ (∃ (w : V), G.adj (round CS (smart_robber G) n).snd w ∧ ¬G.adj (round CS (smart_robber G) n).fst.head w),
      conv {
        to_lhs, congr, rw smart_robber, 
      }, simp, by_contradiction K', rw [pre_smart_robber, rob_strat_fn] at K', simp at K', cases K' with x K', cases K' with h' K',
      push_neg at this, specialize this x, specialize this h'.1, have h'' : ¬G.adj (round CS (smart_robber G) n).fst.head x, exact h'.2, 
      contradiction,
    by_contradiction K', 
    have contradiction: ¬ capture (round CS (smart_robber G) n.succ),
      have this : (smart_robber G).strat.strat (round CS (smart_robber G) n) = some K',
        conv {
          to_lhs, congr, rw smart_robber, 
        }, simp, rw [pre_smart_robber, rob_strat_fn], simp, rw dif_pos K', 
      rw capture, push_neg, intro i, have this: i=0, simp, rw this, clear this, clear i, simp,
      unfold round, simp at h, rw (nat.add_one n).symm at h, rw [pre_round, if_pos h], simp, 
      change (smart_robber G).strat.strat (pre_round CS.strat (smart_robber G).strat n) = _ at this,
      rw this_1, clear this_1,
      suffices this: ¬G.adj (round CS (smart_robber G) n).fst.head (some K'),
        exact rgraph_nadj_imp_neq this,
      exact and.elim_right (classical.some_spec K'),
    exact contradiction cap.1, 
  rw capture at pred_no_cap, push_neg at pred_no_cap, specialize pred_no_cap 0,
  cases cap.1 with i cap', have this: i=0, simp, rw this at cap', clear this, clear i,
  cases n, contradiction,
  rw round, rw (nat.add_one n).symm at h, simp at h, rw [pre_round, if_pos h], simp,
  rw (nat.pred_succ n) at rob_in_place, rw (nat.pred_succ n) at pred_no_cap, 
  rw rob_in_place.symm at pred_no_cap,  simp at pred_no_cap, exact pred_no_cap, exact p,
end

lemma cwg_1_cop_win (G: refl_graph V): cop_win_graph G ↔ k_cop_win G 1 :=
begin
 split, intro cwg, let non := lots_of_cops G,
 let E:= nat.Inf_mem non, rw [cop_win_graph,cop_number] at cwg, rw cwg at E, exact E,
 intro kcw, rw [cop_win_graph,cop_number],
 rw nat.Inf_upward_closed_eq_succ_iff copnumber_upwards_closed 0, 
 split, exact kcw, 
 let x := zero_cops_cant_win G, rw cop_number at x, exact nat.not_mem_of_lt_Inf x,
 repeat {apply_instance},
end

lemma sm_rob_turn0_catch_imp_K1 {G: refl_graph V} {CS: cop_strat G 1} (p: winning_strat_cop CS) : capture (round CS (smart_robber G) 0) → fintype.card V = 1 :=
begin
  intro cap, rw [capture, round, pre_round] at cap, simp at cap,
  cases cap with i cap, have this: i=0, simp, rw this at cap, clear this i,
  have: ∀ w, w= CS.strat.init.head,
  { by_contradiction K, push_neg at K,
    rw [smart_robber] at cap, simp at cap, rw [pre_smart_robber, rob_init_fn] at cap, simp at cap, rw dif_pos K at cap,
    split_ifs at cap,
    exact (rgraph_nadj_imp_neq (some_spec h)) cap,
    exact (some_spec K).symm cap },
  exact fintype.card_eq_one_of_forall_eq this,
end

theorem cwg_has_corner  (G: refl_graph V): cop_win_graph G → has_corner G := 
begin
  intro CW,
  rw cwg_1_cop_win at CW,
  cases CW with CS h,
  rw has_corner,
  let RS := smart_robber G,
  have min : ∃ n:ℕ , n = Inf{n:ℕ | capture (round CS RS n)},
    apply wcs_min_rounds CS h,
  cases min with w hw,
  cases w with w wsucc,
  { apply or.inl, simp at hw,
    have : {n : ℕ | capture (round CS RS n)}.nonempty,
      rw winning_strat_cop at h, specialize h RS, exact h,
    let x := nat.Inf_mem this, simp at x, rw hw.symm at x,
    exact sm_rob_turn0_catch_imp_K1 h x,},
  apply or.inr,
  have cap : capture (round CS RS w.succ),
  { have ne: {n : ℕ | capture (round CS RS n)}.nonempty,
    { unfold winning_strat_cop at h, specialize h RS,
      rwa set.nonempty_def,},
    have w_in: w.succ ∈ {n : ℕ | capture (round CS RS n)},
    { have this: Inf{n : ℕ | capture (round CS RS n)} ∈ {n : ℕ | capture (round CS RS n)},
        exact nat.Inf_mem ne, rw hw.symm at this,
      exact this, },
    exact w_in, },
  have w_succ_odd: odd w.succ,
    have this: w.succ>0,
      exact nat.succ_pos',
    exact smart_capture_cop_move h hw this,
  rw [capture, round] at cap, cases cap with i cap, 
  have this: i=0, simp, rw this at cap, clear this, clear i, simp at cap, 
  rw [pre_round, if_neg (nat.odd_iff_not_even.1 w_succ_odd)] at cap, simp at cap,
  unfold corner_vtx, clear w_succ_odd,
  use (round CS RS w).snd, use (round CS RS w).1.head, split,
  by_contradiction,
  have contra: capture (round CS RS w), unfold capture, use 0, simp, exact h,
  rw nat.succ_eq_add_one at hw, have hw' :Inf {n : ℕ | capture (round CS RS n)} = w+1, exact hw.symm, clear hw,
  have hw := (nat.Inf_upward_closed_eq_succ_iff (capt_upwards_closed) w).mp hw', rename hw' hw,
  cases hw with hw1 hw2, simp at hw2, contradiction, 
  repeat {apply_instance},
  by_contradiction K, rw set.not_subset at K, cases K with a K, cases K with H K,
  rw neighbor_set' at H, simp at H, rw neighbor_set' at K, simp at K,
  cases w,
  have nocap: ¬ (CS.strat.strat (round CS RS 0)).head = (round CS RS 0).snd, 
    suffices this : ¬ G.adj ((round CS RS 0).1.head) (round CS RS 0).snd,
      let x := CS.legal 0 (RS.strat.init CS.strat.init) CS.strat.init, simp at x,
      rw [round, pre_round] at this, simp at this, let y := (rgraph_adj_cmp this x),
      rw [round, pre_round], simp, exact y.symm,
    rw [round, pre_round], simp, change ¬G.adj CS.strat.init.head ((smart_robber G).strat.init CS.strat.init),
    rw [smart_robber], simp, rw [pre_smart_robber, rob_init_fn], simp, 
    unfold round at K, simp at K,
    have this: (∃ (a : V), ¬a = CS.strat.init.head), use a, exact (rgraph_nadj_imp_neq K).symm,
    rw dif_pos this, 
    have that : (∃ (w : V), ¬G.adj CS.strat.init.head w), use a, rw dif_pos that, exact some_spec that,
  contradiction,
  have gt1 : w.succ.succ >1, exact nat.succ_lt_succ (nat.zero_lt_succ w),
  let sameplace_rob := smart_rob_in_place h hw gt1, simp at sameplace_rob, rw sameplace_rob.symm at H,
  have mod : even w.succ,
    let x := smart_capture_cop_move h hw nat.succ_pos', 
    rw odd_succ at x, exact nat.even_iff_not_odd.2 x,
  have sameplace_cop : (round CS RS w.succ).fst.head = (round CS RS w).fst.head,
    rw [round, pre_round, if_pos mod], rw sameplace_cop at K,
  rw [pre_round, if_pos mod] at cap, simp at cap,
  have nocap: ¬ (CS.strat.strat ((round CS RS w).fst, RS.strat.strat (round CS RS w))).head = RS.strat.strat (round CS RS w),
    change ¬ _ = (smart_robber G).strat.strat _ , unfold smart_robber, simp,
  have this : (∃ (w_1 : V), G.adj (round CS RS w).snd w_1 ∧ ¬G.adj (round CS RS w).fst.head w_1),
    use a, split, exact H, exact K,
  rw [pre_smart_robber, rob_strat_fn], simp, rw dif_pos this, 
  suffices cond: ¬G.adj (round CS RS w).fst.head (some this),
    let x := CS.legal 0 (some this) (round CS RS w).fst, simp at x,
    let y := (rgraph_adj_cmp cond x), 
    change ¬(CS.strat.strat ((round CS RS w).fst, (smart_robber G).strat.strat (round CS RS w))).head = _, rw smart_robber, simp, rw [pre_smart_robber, rob_strat_fn], simp,rw dif_pos this, exact y.symm,
  exact and.elim_right (some_spec this),
  contradiction,
end