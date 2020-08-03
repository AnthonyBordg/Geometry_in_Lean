import geometry.manifold.smooth_manifold_with_corners

/-!
This PR implements the product of smooth manifolds with corners. We define the natural instance of
the product of charted space and of the product of smooth manifolds with corners. To this goal, we
also prove that the product map of two smooth maps (times_cont_diff \top) is smooth and we prove
some technical lemmas necessary to do simplifications.
-/

namespace CMP_2020

section analysis__calculus__times_cont_diff


variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]
{s s₁ t u : set E} {f f₁ : E → F} {g : F → G} {x : E} {c : F}
{b : E × F → G}

/--
The first projection on a domain in a product is `C^∞`.
-/
lemma times_cont_diff_on_fst {s : set (E×F)} {n : with_top ℕ} :
  times_cont_diff_on 𝕜 n (prod.fst : E × F → E) s :=
times_cont_diff.times_cont_diff_on times_cont_diff_fst

/--
The second projection on a domain in a product is `C^∞`.
-/
lemma times_cont_diff_on_snd {s : set (E×F)} {n : with_top ℕ} :
  times_cont_diff_on 𝕜 n (prod.snd : E × F → F) s :=
times_cont_diff.times_cont_diff_on times_cont_diff_snd

/-- The product map of two `C^n` functions is `C^n`. -/
lemma times_cont_diff_on.map_prod {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {F' : Type*} [normed_group F'] [normed_space 𝕜 F']
  {s : set E} {t : set E'} {n : with_top ℕ} {f : E → F} {g : E' → F'}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g t) :
  times_cont_diff_on 𝕜 n (prod.map f g) (set.prod s t) :=
begin
  have hs : s.prod t ⊆ (prod.fst) ⁻¹' s := by { rintros x ⟨h_x_1, h_x_2⟩, exact h_x_1, },
  have ht : s.prod t ⊆ (prod.snd) ⁻¹' t := by { rintros x ⟨h_x_1, h_x_2⟩, exact h_x_2, },
  exact (hf.comp (times_cont_diff_on_fst) hs).prod (hg.comp (times_cont_diff_on_snd) ht),
end

end analysis__calculus__times_cont_diff

section data__prod

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

@[simp] lemma prod_map (f : α → γ) (g : β → δ) (p : α × β) : prod.map f g p = (f p.1, g p.2) := rfl

end data__prod

section geometry__manifold__charted_space

variables {H : Type*} {H' : Type*} {M : Type*} {M' : Type*} {M'' : Type*}
[topological_space H] [topological_space M] [charted_space H M]
[topological_space H'] [topological_space M'] [charted_space H' M'] {x : M×M'}

open set

/-- Same thing as `H × H'`. We introduce it for technical reasons: a charted space `M` with model `H`
is a set of local charts from `M` to `H` covering the space. Every space is registered as a charted
space over itself, using the only chart `id`, in `manifold_model_space`. You can also define a product
of charted space `M` and `M'` (with model space `H × H'`) by taking the products of the charts. Now,
on `H × H'`, there are two charted space structures with model space `H × H'` itself, the one coming
from `manifold_model_space`, and the one coming from the product of the two `manifold_model_space` on
each component. They are equal, but not defeq (because the product of `id` and `id` is not defeq to
`id`), which is bad as we know. This expedient of renaming `H × H'` solves this problem. -/
def model_prod (H : Type*) (H' : Type*) := H × H'

section

local attribute [reducible] model_prod

instance model_prod_inhabited {α β : Type*} [inhabited α] [inhabited β] :
  inhabited (model_prod α β) :=
⟨(default α, default β)⟩

instance (H : Type*) [topological_space H] (H' : Type*) [topological_space H'] :
  topological_space (model_prod H H') :=
by apply_instance

/- Next lemma shows up often when dealing with derivatives, register it as simp. -/
@[simp, mfld_simps] lemma model_prod_range_prod_id
  {H : Type*} {H' : Type*} {α : Type*} (f : H → α) :
  range (λ (p : model_prod H H'), (f p.1, p.2)) = set.prod (range f) univ :=
by rw prod_range_univ_eq

end

/-- The product of two charted spaces is naturally a charted space, with the canonical
construction of the atlas of product maps. -/
instance prod_charted_space (H : Type*) [topological_space H]
  (M : Type*) [topological_space M] [charted_space H M]
  (H' : Type*) [topological_space H']
  (M' : Type*) [topological_space M'] [charted_space H' M'] :
  charted_space (model_prod H H') (M × M') :=
{ atlas            :=
    {f : (local_homeomorph (M×M') (model_prod H H')) |
      ∃ g ∈ charted_space.atlas H M, ∃ h ∈ (charted_space.atlas H' M'),
        f = local_homeomorph.prod g h},
  chart_at         := λ x: (M × M'),
    (charted_space.chart_at H x.1).prod (charted_space.chart_at H' x.2),
  mem_chart_source :=
  begin
    intro x,
    simp only with mfld_simps,
  end,
  chart_mem_atlas  :=
  begin
    intro x,
    use (charted_space.chart_at H x.1),
    split,
    { apply chart_mem_atlas _, },
    { use (charted_space.chart_at H' x.2), simp only [chart_mem_atlas, eq_self_iff_true, and_self], }
  end }

section prod_charted_space

variables [topological_space H] [topological_space M] [charted_space H M]
[topological_space H'] [topological_space M'] [charted_space H' M']

@[simp, mfld_simps] lemma prod_charted_space_chart_at :
  (chart_at (model_prod H H') x) = (chart_at H x.fst).prod (chart_at H' x.snd) := rfl

end prod_charted_space

end geometry__manifold__charted_space

section geometry__manifold__smooth_manifold_with_corners

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_group F] [normed_space 𝕜 F] {F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{H : Type*} [topological_space H] {H' : Type*} [topological_space H']
{G : Type*} [topological_space G] {G' : Type*} [topological_space G']
{I : model_with_corners 𝕜 E H} {J : model_with_corners 𝕜 F G}

@[simp, mfld_simps] lemma model_with_corners_prod_to_local_equiv :
  (I.prod J).to_local_equiv = (I.to_local_equiv).prod (J.to_local_equiv) :=
begin
  ext1 x,
  { refl, },
  { intro x, refl, },
  { simp only [set.univ_prod_univ, model_with_corners.source_eq, local_equiv.prod_source], }
end

@[simp, mfld_simps] lemma model_with_corners_prod_coe
  (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') :
  (I.prod I' : _ × _ → _ × _) = prod.map I I' := rfl

@[simp, mfld_simps] lemma model_with_corners_prod_coe_symm
  (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') :
  ((I.prod I').symm : _ × _ → _ × _) = prod.map I.symm I'.symm := rfl

/-- The product of two smooth local homeomorphisms is smooth. -/
lemma times_cont_diff_groupoid_prod
  {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
  {e : local_homeomorph H H} {e' : local_homeomorph H' H'}
  (he : e ∈ times_cont_diff_groupoid ⊤ I) (he' : e' ∈ times_cont_diff_groupoid ⊤ I') :
  e.prod e' ∈ times_cont_diff_groupoid ⊤ (I.prod I') :=
begin
  cases he with he he_symm,
  cases he' with he' he'_symm,
  simp only at he he_symm he' he'_symm,
  split;
  simp only [local_equiv.prod_source, local_homeomorph.prod_to_local_equiv],
  { have h3 := times_cont_diff_on.map_prod he he',
    rw [← model_with_corners.image I _, ← model_with_corners.image I' _,
    set.prod_image_image_eq] at h3,
    rw ← model_with_corners.image (I.prod I') _,
    exact h3, },
  { have h3 := times_cont_diff_on.map_prod he_symm he'_symm,
    rw [← model_with_corners.image I _, ← model_with_corners.image I' _,
    set.prod_image_image_eq] at h3,
    rw ← model_with_corners.image (I.prod I') _,
    exact h3, }
end

/-- The product of two smooth manifolds with corners is naturally a smooth manifold with corners. -/
instance prod_smooth_manifold_with_corners {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  (M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] :
  smooth_manifold_with_corners (I.prod I') (M×M') :=
{ compatible :=
  begin
    rintros f g ⟨f1, hf1, f2, hf2, hf⟩ ⟨g1, hg1, g2, hg2, hg⟩,
    rw [hf, hg, local_homeomorph.prod_symm, local_homeomorph.prod_trans],
    have h1 := has_groupoid.compatible (times_cont_diff_groupoid ⊤ I) hf1 hg1,
    have h2 := has_groupoid.compatible (times_cont_diff_groupoid ⊤ I') hf2 hg2,
    exact times_cont_diff_groupoid_prod h1 h2,
  end }


end geometry__manifold__smooth_manifold_with_corners

section

end


end CMP_2020
