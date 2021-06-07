import graphtheory
import data.fintype.basic
import set_theory.zfc

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
 λ x, if h : ∃ w, w ≠ x.head then 
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
    erw c_nocheat,
    simp,
    erw r_nocheat,
    simp,
  },
  rw h, exact hyp,
end

--If the cop did not capture at round w but captured at round w+1, then the capture happened on the cop move
theorem mid_round_capt [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V} {CS: cop_strat G 1} {w: ℕ } (bef: ¬ capture (round CS (smart_robber G) w)) (aft: capture (round CS (smart_robber G) w.succ)):
capture (CS.cop_strat (round CS (smart_robber G) w), (round CS (smart_robber G) w).2):=
begin
  by_contradiction K,
  let pos := (CS.cop_strat (round CS (smart_robber G) w), (round CS (smart_robber G) w).2),
  by_cases h: G.adj pos.1.head (round CS (smart_robber G) w).2,
  -- Case 1: The cops vtx is adjacent to the robber vtx 
  -- Proof strategy: Then the robber can stay in place, implying no capture (for at least round w.succ)
  { by_cases h': ∃ w, G.adj pos.2 w ∧ ¬ G.adj pos.1.head w,
  -- Two cases: Either the robber still has an escape route or it stays in place
    { have move : (smart_robber G).rob_strat pos  = classical.some h',
      { rw smart_robber,
        simp,
        rw dif_pos h',
      },
      have nocap: ¬ capture (round CS (smart_robber G) w.succ),
      { unfold capture,
        simp,
      intro x,
      have : x=0, simp, rw this,
      unfold round,
      rw move,
      simp,
      exact (rgraph_vtx_neq pos.1.head h').symm,
      },
      contradiction,
    },
    have move: (smart_robber G).rob_strat pos = pos.2,
    { rw smart_robber,
      simp,
      rw dif_neg h',
    },
    have nocap : ¬ capture (round CS (smart_robber G) w.succ), 
    { unfold capture, 
      simp,
      intro x,
      have : x=0, simp, rw this,
      unfold round,
      simp,
      rw move,
      rw capture at K, simp at K, specialize K 0, simp at K,
      exact K,
    },
    contradiction,
  },
  --Case 2: The cop vtx is not adjacent to the robber vtx+there is an escape route
  --Then, the robber will move to said vtx and avoid capture
  have h' : ∃ w, G.adj pos.2 w ∧ ¬ G.adj pos.1.head w,
  { use (round CS (smart_robber G) w).2,
    split,
    {exact G.selfloop pos.2,},
    exact h,
  },
  have nocap : ¬ capture (round CS (smart_robber G) w.succ),
  { have move : (smart_robber G).rob_strat pos  = classical.some h',
      { rw smart_robber,
        simp,
        rw dif_pos h',
      },
    unfold capture,
    simp,
    intro x,
    have : x=0,
      simp,
    rw this,
    unfold round,
    rw move,
    simp,
    exact (rgraph_vtx_neq pos.1.head h').symm,
  },
  contradiction,
end

--With the same premise as above, the robber does not move on round w+1 in response to cop move.
lemma rob_in_place [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V} {CS: cop_strat G 1} {w: ℕ } (bef: ¬ capture (round CS (smart_robber G) w)) (aft: capture (round CS (smart_robber G) w.succ)) :
(round CS (smart_robber G) w.succ).2 = (round CS (smart_robber G) w).2 :=
begin
  have mid_capt:= mid_round_capt bef aft,
  let RS:= smart_robber G, 
  unfold round, simp,
    exact RS.rob_nocheat (CS.cop_strat (round CS (smart_robber G) w), (round CS (smart_robber G) w).snd) mid_capt,
end


--A smart robber getting caught at the zeroth round implies graph is only one vertex (is trivially K1 by reflexivity)
lemma zero_cap_implies_K1 [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V}
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

--A smart robber getting caught at the first round implies the graph has a corner
lemma round1_cap_implies_corner [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V}
  (CS: cop_strat G 1) (cap: capture (round CS (smart_robber G) 1))
  : has_corner G :=
  begin
    rw has_corner, apply or.inr,
    rw [capture, round] at cap, cases cap with i cap,
    have : i=0, simp, rw this at cap, simp at cap,
    rw smart_robber at cap, simp at cap,
    sorry,
  end


theorem cwg_has_corner [fintype V] [decidable_eq V] [inhabited V] (G: refl_graph V): 
cop_win_graph G → has_corner G := 
begin
  --Setup
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
  --Divide into cases based on when the capture happens: 
  cases w with w wsucc,
  --Zero case: If the robber and cop start on the same vertex, then the graph is just a single vertex
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
    have: ∀ w, w= CS.cop_init.head,
    { by_contradiction K,
      push_neg at K,
      change _ = (smart_robber G).rob_init _ at hi,
      have x : rob_init_fn G CS.cop_init ≠ CS.cop_init.head,
      { unfold rob_init_fn,
        rw dif_pos K, 
        by_cases h: ∃ (w : V), ¬G.adj CS.cop_init.head w,
        { rw dif_pos h,
          exact rgraph_vtx_neq' CS.cop_init.head h,
        },
        rw dif_neg h,
        push_neg at h,
        exact some_spec K,
      },
      have y : (smart_robber G).rob_init CS.cop_init ≠ rob_init_fn G CS.cop_init,
        exact ne_of_eq_of_ne hi.symm x.symm,
      contradiction,
    },
    exact fintype.card_eq_one_of_forall_eq this,
  },
  --Successor Case: If it takes the cop at least one move, look at second-to-last move of the cop
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
  have w_nocap : ¬ capture (round CS RS w),
  { suffices : w ∉ {n : ℕ | capture (round CS RS n)},
    { exact this,},
    exact and.right ((nat.Inf_upward_closed_eq_succ_iff capt_upwards_closed w).1 hw.symm),
  },
  have mid_capt:= mid_round_capt w_nocap w_cap,
  apply or.inr,
  use (round CS RS w).2,
  use (round CS RS w).1.head,
  split,
  { by_contradiction sps, simp at sps,
    have uhoh : capture (round CS RS w),
    { rw capture,
      use 0, simp, exact sps,
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
  have rob_in_place: (round CS RS w.succ).2 = (round CS RS w).2,
  { unfold round, simp,
    exact RS.rob_nocheat (CS.cop_strat (round CS (smart_robber G) w), (round CS (smart_robber G) w).snd) mid_capt,
  },
  suffices : ¬∃ x, G.adj (round CS RS w).snd x ∧ ¬ G.adj (round CS RS w).fst.head x,
  { push_neg at this,
    intros v hv,
    rw neighbor_set' at hv, simp at hv,
    specialize this v hv,
    exact this,
  },
  cases w with w wsucc,
  { by_contradiction K,

  },

  
  -- unfold round at rob_in_place,
  -- simp at rob_in_place,
  -- change (smart_robber G).rob_strat _  = _ at rob_in_place,
  -- unfold smart_robber at rob_in_place, simp at rob_in_place,

  
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


