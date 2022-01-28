import graphtheory
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

--If the cop captures at some round n, then he captures for all m >= n
theorem capt_upwards_closed [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V} {n: ℕ} {CS: cop_strat G n} {RS: rob_strat G n} : ∀ k1 k2 : ℕ , k1 ≤ k2 → k1 ∈ {n:ℕ | capture (round CS RS n)} → k2 ∈ {n:ℕ | capture (round CS RS n)} :=
begin
  intros k1 k2 le inc,
  suffices : ∀ k1, k1 ∈ {n:ℕ | capture (round CS RS n)} → k1.succ ∈ {n:ℕ | capture (round CS RS n)},
  { exact nat.le_rec_on le this inc,},
  intros k1 hyp,
  simp at hyp, simp,
  have r_nocheat: RS.rob_strat (round CS RS k1) = (round CS RS k1).2,
    exact RS.rob_nocheat (round CS RS k1) hyp,
  have c_nocheat: CS.cop_strat (round CS RS k1) = (round CS RS k1).1,
    exact CS.cop_nocheat (round CS RS k1) hyp,
  have h: round CS RS k1.succ = round CS RS k1,
  { unfold round,
    rw c_nocheat,
    simp,
  },
  rw h, exact hyp,
end

lemma or_iff_right {a b : Prop} (ha : ¬ a) : a ∨ b ↔ b := ⟨λ h, h.resolve_left ha, or.inr⟩

theorem mod2_zero_or_one : ∀ n : ℕ, n%2=1 ∨ n%2=0 :=
begin
  intro n,
  rw nat.even_iff.symm, rw nat.odd_iff.symm,
  exact (nat.even_or_odd n).symm,
end

theorem smart_capture_cop_move [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V} {CS: cop_strat G 1} {n : ℕ} (cap :capture (round CS (smart_robber G) n)) (gt: n > 0) : n%2=1 :=
begin
  by_contradiction K, 
  have K': n%2=0,
    exact (or_iff_right K).1 (mod2_zero_or_one n),
  have n_is_succ : (∃ m : ℕ, m.succ = n),
    use n.pred, 
    have this: n ≠ 0, linarith,
    rw nat.succ_eq_one_add, rw nat.pred_eq_sub_one, 
    sorry,
  unfold capture at cap, 
  cases cap with i cap, have this: i=0, simp, rw this at cap, simp at cap,
  cases n_is_succ with m succ,
  sorry,
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
    exact smart_capture_cop_move cap this,
  rw [capture, round] at cap, cases cap with i cap, 
  have this: i=0, simp, rw this at cap, simp at cap, 
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
    have this : x=0, simp, rw this,
    have rob_move: (RS.rob_strat (round CS RS w)) = some K,
      change ((smart_robber G).rob_strat (round CS RS w)) = some K,
      unfold smart_robber,simp,
      rw dif_pos K,
      sorry,
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


