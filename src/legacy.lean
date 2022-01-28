import graphtheory
import dismantlable
import data.fintype.basic
import set_theory.zfc

open finset
open classical

variables {V: Type} [fintype V] [inhabited V]

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

lemma cop_adj_rob [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V} {n:ℕ }
  {CS: cop_strat G 1} (nocap: ¬ capture (round CS (smart_robber G) n)) (cap: capture (round CS (smart_robber G) n.succ))
: G.adj (round CS (smart_robber G) n).1.head (round CS (smart_robber G) n).2 :=
begin
  let rip := rob_in_place nocap cap, 
  unfold capture at cap,
  cases cap with i hi,
  have :i=0, simp, rw this at hi, simp at hi,
  have adj: G.adj (round CS (smart_robber G) n).1.head (round CS (smart_robber G) n.succ).1.head,
  { let adj' := CS.cop_legal 0 (round CS (smart_robber G) n).2 (round CS (smart_robber G) n).1,
    simp at adj', 
    have h : (CS.cop_strat (round CS (smart_robber G) n)).nth 0 = (round CS (smart_robber G) n.succ).1.head,
      unfold round, simp,
    simp at h, 
    exact rgraph_adj_eq_trans adj' h,
  },
  exact rgraph_adj_eq_trans adj (eq.trans hi rip),
end

-- def rob_init_fn {V: Type} [fintype V] [decidable_eq V] (G: refl_graph V) : vector V 1 → V := 
--  λ x, if h : ∃ w, w ≠ x.head then 
--  (if g: ∃ w, ¬ G.adj x.head w then some g else some h)
--  else x.head

--A smart robber getting caught at the first round implies the graph has a corner
lemma round1_cap_implies_corner [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V}
  {CS: cop_strat G 1} (nocap: ¬ capture (round CS (smart_robber G) 0)) (cap: capture (round CS (smart_robber G) 1))
  : has_corner G :=
  begin
    rw has_corner, apply or.inr,
    use (round CS (smart_robber G) 0).2,
    use (round CS (smart_robber G) 0).1.head,
    split,
    { by_contradiction K,
      have :  capture (round CS (smart_robber G) 0),
        { unfold capture, use 0,
          simp, simp at K, exact K,},
      contradiction, 
    },
    intros v hv, unfold neighbor_set' at hv, simp at hv,
    unfold neighbor_set', simp,
    by_contradiction K,
    have f: ∃ (a : V), ¬a = CS.cop_init.head,
    { use v, rw [round, smart_robber] at K, simp at K,
      exact (rgraph_nadj_imp_neq K).symm,
    },
    have g: ∃ w, ¬ G.adj CS.cop_init.head w,
      use v,
    have wrong: (smart_robber G).rob_init CS.cop_init = some g,
    { unfold smart_robber, simp,
      rw rob_init_fn, simp,
      rw dif_pos f, rw dif_pos g,
    },
    apply classical.some_spec g, rw wrong.symm,
    let ad := cop_adj_rob nocap cap, simp at ad,
    unfold round at ad, simp at ad, exact ad,
  end

-- rob_strat:= λ x , if h : ∃ w, G.adj x.2 w ∧ ¬ G.adj x.1.head w then some h else x.2,
lemma roundn_cap_implies_corner [fintype V] [decidable_eq V] [inhabited V] {G: refl_graph V} {n: ℕ }
  {CS: cop_strat G 1} (nocap: ¬ capture (round CS (smart_robber G) n)) (cap: capture (round CS (smart_robber G) n.succ))
  : has_corner G :=
  begin
    cases n with n m,
    { exact round1_cap_implies_corner nocap cap,},
    rw has_corner, apply or.inr,
    use (round CS (smart_robber G) n.succ).2,
    use (round CS (smart_robber G) n.succ).1.head,
    split,
    { by_contradiction K,
      have :  capture (round CS (smart_robber G) n.succ),
        { unfold capture, use 0,
          simp, simp at K, exact K,},
      contradiction, 
    },
    intros v hv, unfold neighbor_set' at hv, simp at hv,
    unfold neighbor_set', simp,
    by_contradiction K,
    have : (round CS (smart_robber G) n.succ).2 = (round CS (smart_robber G) n).2,
    { unfold round, simp,
      let mid:= (CS.cop_strat (round CS (smart_robber G) n), (round CS (smart_robber G) n).snd), 
      suffices : ¬ ∃ w, G.adj mid.2 w ∧ ¬ G.adj mid.1.head w,
      { rewrite {(smart_robber G).rob_strat _ = _}smart_robber,
      },
    },
  end


theorem cwg_has_corner [fintype V] [decidable_eq V] [inhabited V] (G: refl_graph V): 
cop_win_graph G → has_corner G := 
begin
  --Setup
  intro CW,
  rw [cop_win_graph,cop_number] at CW,
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
  
end
