import dismantlable

variables {V: Type} [fintype V] [inhabited V] [decidable_eq V] {c: V}

open classical
noncomputable theory 

def induced_subgraph (S: set V) (G: refl_graph V) : refl_graph {v:V// v ∈ S} :=
{ adj := λ a b, G.adj a b, 
  sym :=  λ a b h, G.sym h,
  selfloop := begin intro a, apply G.selfloop end }

def ind_subgraph_one_vtx (v: V) (G: refl_graph V) : refl_graph {w : V // w ≠ v}
:= induced_subgraph (λ x, x ≠ v) G

def cing_vtx_subtype (v: V) (G: refl_graph V) (h: corner_vtx G v) : {w: V // w ≠ v}
:= some (subtype.exists'.1 h)

def not_corner_vtx_subtype (v: V) (G: refl_graph V) (h: v ≠ c) : {w: V // w ≠ c} := ⟨v,h⟩

def retract (G: refl_graph V) (H:= ind_subgraph_one_vtx c G) : Prop :=
∃ f: graph_hom G H, ∀ v ≠ c, v = f.to_fun(v)

def retract_fun (G: refl_graph V) (H:= ind_subgraph_one_vtx c G) (h : corner_vtx G c) : 
V → {w: V // w ≠ c} := λ v, if eq: v = c then cing_vtx_subtype c G h else not_corner_vtx_subtype v G eq

lemma retract_fun_works_pos_refl (G: refl_graph V) (H:= ind_subgraph_one_vtx c G) (h: corner_vtx G c) :
H.adj (retract_fun G H h c) (cing_vtx_subtype c G h) :=
begin
  suffices : retract_fun G H h c = cing_vtx_subtype c G h,
  rw this, exact H.selfloop (cing_vtx_subtype c G h),
  rw retract_fun, simp,
end

lemma retract_fun_works_neg_refl (G: refl_graph V) (H:= ind_subgraph_one_vtx c G) (h: corner_vtx G c) :
∀ (v: V) (ne: v ≠ c), H.adj (retract_fun G H h v) (not_corner_vtx_subtype v G ne) :=
begin
  intros v ne,
  suffices : retract_fun G H h v = not_corner_vtx_subtype v G ne,
  rw this, exact H.selfloop (not_corner_vtx_subtype v G ne),
  rw retract_fun, simp, rw dif_neg ne,
end

lemma retract_fun_works_pos_adj (G: refl_graph V) (H:= ind_subgraph_one_vtx c G) (h: corner_vtx G c) :
∀ (v: V) (adj: G.adj c v), H.adj (retract_fun G H h c) (retract_fun G H h v) :=
begin
  intros v G_adj, by_cases eq: v = c,
  rw eq, exact H.selfloop (retract_fun G H h c),
  rw retract_fun, simp, rw [dif_neg eq, cing_vtx_subtype, not_corner_vtx_subtype],
  suffices : G.adj (classical.some h) v, {sorry,},
  sorry,
end

def corner_retract (G: refl_graph V) (H:= ind_subgraph_one_vtx c G) (h : corner_vtx G c): graph_hom G H :=
{ to_fun := retract_fun G H h,
  map_edges :=
  begin
    intros v w adj, by_cases v_eq: v=c, by_cases w_eq: w = c,
    rw [v_eq, w_eq], exact H.selfloop (retract_fun G H h c),
    rw v_eq, rw v_eq at adj, exact retract_fun_works_pos_adj G H h w adj,
    sorry, --another by_cases
  end
}


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
    intros K cap,
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
  sorry,
end
