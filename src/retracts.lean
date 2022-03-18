import dismantlable

variables {V: Type} [fintype V] [inhabited V] [decidable_eq V] {c: V}

noncomputable theory 

def induced_subgraph (S: set V) (G: refl_graph V) : refl_graph {v:V// v ∈ S} :=
{ adj := λ a b, G.adj a b, 
  sym :=  λ a b h, G.sym h,
  selfloop := begin intro a, apply G.selfloop end }

def ind_subgraph_one_vtx (v: V) (G: refl_graph V) : refl_graph {w : V // w ≠ v}
:= induced_subgraph (λ x, x ≠ v) G

-- structure fold (G: refl_graph V) (H:= induced_subgraph {v: V | v ≠ c} G)  := 
--   (f: graph_hom G H)
--   (id: ∀ v ≠ c, v = f.to_fun(v))
  -- (corner: corner_cmp G c ↑(f.to_fun(c)))

def retract (G: refl_graph V) (H:= ind_subgraph_one_vtx c G) : Prop :=
∃ f: graph_hom G H, ∀ v ≠ c, v = f.to_fun(v)

def to_subtype {G: refl_graph V} (h: corner_vtx G c) : {w : V // w ≠ c} :=
begin
  rw corner_vtx at h, have h2: ∃ (v: V) (neq: v ≠ c), neighbor_set' G c ⊆ neighbor_set' G v,
  
end

def corner_retract (G: refl_graph V) (H:= ind_subgraph_one_vtx c G) (h : corner_vtx G c): graph_hom G H :=
{
  to_fun:= λ v, if v = c then cornering_vtx G c h else v
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
