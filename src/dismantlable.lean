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

/-TODO: This theorem. It uses the "second to last" move of the cop, which might be a little hard to encode-/
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
  rw winning_strat_cop at h,
  let RS: rob_strat G 1,
  {
/-Here, what to prove?-/
    sorry,
  },
  cases h RS with n hn,
  induction n,
  {
    rw capture at hn,
    cases hn with i hi,
    have zero: i=0,
      simp,
    rw zero at hi,
    use (round CS RS 0).fst.nth 0,
    simp,
    sorry,
  },
  {
    let before:= round CS RS n_n,
    use before.2,
    use before.1.head,
    split,
    {
      by_contradiction k,
      sorry,
    },    
  },
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


