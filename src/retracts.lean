import dismantlable

variables {V: Type} [fintype V] [inhabited V] [decidable_eq V] {c: V}

open classical
noncomputable theory

-- Induced subgraph generated by a vertex set S ⊆ V
def induced_subgraph (S: set V) (G: refl_graph V) : refl_graph {v:V// v ∈ S} :=
{ adj := λ a b, G.adj a b,
  sym :=  λ a b h, G.sym h,
  selfloop := begin intro a, apply G.selfloop end}

lemma ind_subgraph_is_induced {G: refl_graph V} : ∀ S: set V, ∀ v w : {v:V// v ∈ S}, G.adj v w → (induced_subgraph S G).adj v w :=
begin
  intros S v w Gadj, rw induced_subgraph, simp, exact Gadj,
end

-- Induced subgraph of one vertex removed
def ind_subgraph_one_vtx (v: V) (G: refl_graph V) : refl_graph {w : V // w ≠ v}
:= induced_subgraph (λ x, x ≠ v) G

-- v is the cornered vtx. cing_vtx is the vtx cornering v
def cing_vtx {v: V} {G: refl_graph V} (h: corner_vtx G v) :=
some h

-- a vertex can't corner itself
theorem cing_vtx_distinct {v: V} {G: refl_graph V} (h: corner_vtx G v) : cing_vtx h ≠ v :=
begin
  obtain ⟨hw1, hw2⟩ := (some_spec h),
  exact hw1
end

-- subset inclusion property of corners
theorem cing_vtx_nhds {v: V} {G: refl_graph V} (h: corner_vtx G v) : neighbor_set' G v ⊆ neighbor_set' G (cing_vtx h) :=
begin
  obtain ⟨hw1, hw2⟩ := (some_spec h),
  exact hw2
end

lemma cing_vtx_nhds_vtx {v: V} {G: refl_graph V} (h: corner_vtx G v) : ∀ w: V, G.adj v w → G.adj (cing_vtx h) w :=
begin
  obtain ⟨hw1, hw2⟩ := (some_spec h),
  intros w hw, conv at hw2 {congr, rw neighbor_set', skip, rw neighbor_set'}, 
  exact set.mem_of_subset_of_mem hw2 hw,
end

-- from type V to subtype {w: V // w ≠ v}, for cornering vtxs
def cing_vtx_subtype {v: V} {G: refl_graph V} (h: corner_vtx G v) : {w: V // w ≠ v}
:= ⟨cing_vtx h, cing_vtx_distinct h⟩

-- correctness of cing_vtx_subtype
theorem val_cing_vtx_subtype {v: V} {G: refl_graph V} (h: corner_vtx G v) : (cing_vtx_subtype h).val = cing_vtx h := rfl

-- from type V to subtype {w: V // w ≠ v}, for cornering vtxs
def not_corner_vtx_subtype (v: V) (G: refl_graph V) (h: v ≠ c) : {w: V // w ≠ c} := ⟨v,h⟩

def retract (G: refl_graph V) (H := ind_subgraph_one_vtx c G) : Prop :=
∃ f: graph_hom G H, ∀ v ≠ c, v = f.to_fun(v)

def retract_fun (G: refl_graph V) (H:= ind_subgraph_one_vtx c G) (h : corner_vtx G c) :
V → {w: V // w ≠ c} := λ v, if eq: v = c then cing_vtx_subtype h else ⟨v,eq⟩

--retract_fun works correctly
lemma retract_fun_works_pos_refl (G: refl_graph V) (H:= ind_subgraph_one_vtx c G) (h: corner_vtx G c) :
H.adj (retract_fun G H h c) (cing_vtx_subtype h) :=
begin
  suffices : retract_fun G H h c = cing_vtx_subtype h,
  rw this, exact H.selfloop (cing_vtx_subtype h),
  rw retract_fun, simp,
end

lemma retract_fun_works_neg_refl (G: refl_graph V) (H:= ind_subgraph_one_vtx c G) (h: corner_vtx G c) :
∀ (v: V) (ne: v ≠ c), H.adj (retract_fun G H h v) (not_corner_vtx_subtype v G ne) :=
begin
  intros v ne,
  suffices : retract_fun G H h v = not_corner_vtx_subtype v G ne,
  rw this, exact H.selfloop (not_corner_vtx_subtype v G ne),
  rw retract_fun, simp, rw [dif_neg ne, not_corner_vtx_subtype],
end

-- retract_fun preserves edge relations
lemma retract_fun_works_pos_adj (G: refl_graph V) (h: corner_vtx G c) :
∀ (v: V) (adj: G.adj c v), (ind_subgraph_one_vtx c G).adj (retract_fun G (ind_subgraph_one_vtx c G) h c) (retract_fun G (ind_subgraph_one_vtx c G) h v) :=
begin
  intros v hyp, by_cases eq: v=c, rw eq, exact (ind_subgraph_one_vtx c G).selfloop (retract_fun G (ind_subgraph_one_vtx c G) h c),
  rw retract_fun, simp, rw [dif_neg eq], rw cing_vtx_subtype,
  have adj : G.adj (cing_vtx h) v,
    exact cing_vtx_nhds_vtx h v hyp,
  rw ind_subgraph_one_vtx, 
  exact ind_subgraph_is_induced (λ (x : V), x ≠ c) ⟨cing_vtx h, _⟩ ⟨v, eq⟩ adj,
end

--QUESTIONS ABOUT OPT_PARAM
-- lemma retract_fun_works_pos_adj' (G: refl_graph V) (H := ind_subgraph_one_vtx c G) (h: corner_vtx G c) :
-- ∀ (v: V) (adj: G.adj c v), H.adj (retract_fun G H h c) (retract_fun G H h v) :=
-- begin
--   intros v hyp, by_cases eq: v=c, rw eq, exact H.selfloop (retract_fun G H h c),
--   rw retract_fun, simp, rw [dif_neg eq], rw cing_vtx_subtype,
--   have adj : G.adj (cing_vtx h) v,
--     exact cing_vtx_nhds_vtx h v hyp,
--   let res := ind_subgraph_is_induced (λ (x : V), x ≠ c) ⟨cing_vtx h, _⟩ ⟨v, eq⟩ adj,
--   change (ind_subgraph_one_vtx c G).adj _ _,

-- end

def corner_retract (G: refl_graph V) (h : corner_vtx G c): graph_hom G (ind_subgraph_one_vtx c G) :=
{ to_fun := retract_fun G (ind_subgraph_one_vtx c G) h,
  map_edges :=
  begin
    let H := (ind_subgraph_one_vtx c G),
    intros v w adj, by_cases v_eq: v=c, by_cases w_eq: w = c,
    rw [v_eq, w_eq], exact H.selfloop (retract_fun G H h c),
    rw v_eq, rw v_eq at adj, exact retract_fun_works_pos_adj G h w adj,
    by_cases w_eq: w=c,
    rw retract_fun, simp, rw [dif_neg v_eq, dif_pos w_eq, cing_vtx_subtype], 
    rw [w_eq, rgraph_adj_symm] at adj,
    let cing_vtx_adj := cing_vtx_nhds_vtx h v adj,
    exact ind_subgraph_is_induced (λ (x : V), x ≠ c) ⟨v, v_eq⟩ ⟨cing_vtx h, _⟩ (rgraph_adj_symm.1 cing_vtx_adj),
    rw retract_fun, simp, rw [dif_neg v_eq, dif_neg w_eq],
    exact ind_subgraph_is_induced (λ (x : V), x ≠ c) ⟨v, v_eq⟩ ⟨w, w_eq⟩ adj,
  end
}

def image_strat_init {n: ℕ} (G: refl_graph V) (h: corner_vtx G c) (CS: cop_strat G n) : vector {w // w ≠ c} n := vector.map (corner_retract G h).to_fun CS.cop_init

def cr_pos_to_retract {n: ℕ} (G: refl_graph V) (h: corner_vtx G c) (s: vector V n × V) :  vector {w // w ≠ c} n × {w // w ≠ c} := (vector.map (corner_retract G h).to_fun s.1, (corner_retract G h).to_fun s.2)

def cr_pos_from_retract {n: ℕ} (G: refl_graph V)(h: corner_vtx G c) (s: vector {w // w ≠ c} n × {w // w ≠ c}) : vector V n × V  := (vector.map (λ t, ↑t) s.1, s.2)

def image_strat_fun {n: ℕ} (G: refl_graph V) (h: corner_vtx G c) (CS: cop_strat G n) : vector {w // w ≠ c} n × {w // w ≠ c} → vector {w // w ≠ c} n := λ s, vector.map (corner_retract G h).to_fun (CS.cop_strat (cr_pos_from_retract G h s))

def image_strat {n: ℕ} (G: refl_graph V) (h: corner_vtx G c) (CS: cop_strat G n)
: cop_strat (ind_subgraph_one_vtx c G) n :=
{
  cop_init := image_strat_init G h CS,
  cop_strat := image_strat_fun G h CS,
  cop_nocheat :=
  begin
    sorry,
  end,
  cop_legal :=
  begin
    intros i v P, rw image_strat_fun, simp,
    let move := ((corner_retract G h).to_fun ((CS.cop_strat (cr_pos_from_retract G h (P, v))).nth i)), 
    suffices : G.adj (P.nth i) move,
      exact ind_subgraph_is_induced (λ (x : V), x ≠ c) (P.nth i) move this,
    let G_legal := CS.cop_legal i v (vector.map (λ t, ↑t) P), simp at G_legal,
    sorry,
  end,
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


def dismantling_order (G: refl_graph V) : list V → Prop
| [] := G ≅ singleton_graph
| (a::L) := (corner_vtx G a) ∧ dismantling_order L

def dismantlable_graph (G: refl_graph V) := ∃ L, dismantling_order G L
