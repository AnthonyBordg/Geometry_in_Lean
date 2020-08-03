import geometry.algebra.lie_group

namespace CMP_2020

section has_mul

variables {G : Type*} [has_mul G]

/-- `left_mul g` denotes left multiplication by `g` -/
@[to_additive "`left_add g` denotes left addition by `g`"]
def left_mul : G → G → G := λ g : G, λ x : G, g * x

/-- `right_mul g` denotes right multiplication by `g` -/
@[to_additive "`right_add g` denotes right addition by `g`"]
def right_mul : G → G → G := λ g : G, λ x : G, x * g

end has_mul

section times_cont_diff

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]
{s s₁ t u : set E} {f f₁ : E → F} {g : F → G} {x : E} {c : F}
{b : E × F → G}

/--
The first projection at a point in a product is `C^∞`.
-/
lemma times_cont_diff_at_fst {p : E × F} {n : with_top ℕ} :
  times_cont_diff_at 𝕜 n (prod.fst : E × F → E) p :=
times_cont_diff_fst.times_cont_diff_at

/--
The first projection within a domain at a point in a product is `C^∞`.
-/
lemma times_cont_diff_within_at_fst {s : set (E × F)} {p : E × F} {n : with_top ℕ} :
  times_cont_diff_within_at 𝕜 n (prod.fst : E × F → E) s p :=
times_cont_diff_fst.times_cont_diff_within_at

lemma times_cont_diff_add {n : with_top ℕ} : times_cont_diff 𝕜 n (λp : F × F, p.1 + p.2) :=
begin
  apply is_bounded_linear_map.times_cont_diff,
  exact is_bounded_linear_map.add is_bounded_linear_map.fst is_bounded_linear_map.snd,
end

/-- The sum of two `C^n`functions is `C^n`. -/
lemma times_cont_diff.add {n : with_top ℕ} {f g : E → F}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) : times_cont_diff 𝕜 n (λx, f x + g x) :=
times_cont_diff_add.comp (hf.prod hg)

lemma times_cont_diff_neg {n : with_top ℕ} : times_cont_diff 𝕜 n (λp : F, -p) :=
begin
  apply is_bounded_linear_map.times_cont_diff,
  exact is_bounded_linear_map.neg is_bounded_linear_map.id
end

/-- The negative of a `C^n`function is `C^n`. -/
lemma times_cont_diff.neg {n : with_top ℕ} {f : E → F} (hf : times_cont_diff 𝕜 n f) :
  times_cont_diff 𝕜 n (λx, -f x) :=
times_cont_diff_neg.comp hf

section prod_map
variables {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{n : with_top ℕ}

open set

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
lemma times_cont_diff_within_at.prod_map'
  {s : set E} {t : set E'} {f : E → F} {g : E' → F'} {p : E × E'}
  (hf : times_cont_diff_within_at 𝕜 n f s p.1) (hg : times_cont_diff_within_at 𝕜 n g t p.2) :
  times_cont_diff_within_at 𝕜 n (prod.map f g) (set.prod s t) p :=
(hf.comp p times_cont_diff_within_at_fst (prod_subset_preimage_fst _ _)).prod
  (hg.comp p times_cont_diff_within_at_snd (prod_subset_preimage_snd _ _))

lemma times_cont_diff_within_at.prod_map
  {s : set E} {t : set E'} {f : E → F} {g : E' → F'} {x : E} {y : E'}
  (hf : times_cont_diff_within_at 𝕜 n f s x) (hg : times_cont_diff_within_at 𝕜 n g t y) :
  times_cont_diff_within_at 𝕜 n (prod.map f g) (set.prod s t) (x, y) :=
times_cont_diff_within_at.prod_map' hf hg

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
lemma times_cont_diff_at.prod_map {f : E → F} {g : E' → F'} {x : E} {y : E'}
  (hf : times_cont_diff_at 𝕜 n f x) (hg : times_cont_diff_at 𝕜 n g y) :
  times_cont_diff_at 𝕜 n (prod.map f g) (x, y) :=
begin
  rw times_cont_diff_at at *,
  convert hf.prod_map hg,
  simp only [univ_prod_univ]
end

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
lemma times_cont_diff_at.prod_map' {f : E → F} {g : E' → F'} {p : E × E'}
  (hf : times_cont_diff_at 𝕜 n f p.1) (hg : times_cont_diff_at 𝕜 n g p.2) :
  times_cont_diff_at 𝕜 n (prod.map f g) p :=
by cases p; exact times_cont_diff_at.prod_map hf hg

/-- The product map of two `C^n` functions is `C^n`. -/
lemma times_cont_diff.prod_map
  {f : E → F} {g : E' → F'}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) :
  times_cont_diff 𝕜 n (prod.map f g) :=
begin
  rw times_cont_diff_iff_times_cont_diff_at at *,
  exact λ ⟨x, y⟩, (hf x).prod_map (hg y)
end

end prod_map

end times_cont_diff

section times_cont_mdiff

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
-- declare a smooth manifold `M` over the pair `(E, H)`.
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M]
-- declare a smooth manifold `M'` over the pair `(E', H')`.
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M']
-- declare a smooth manifold `N` over the pair `(F, G)`.
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
{N : Type*} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N]
-- declare a smooth manifold `N'` over the pair `(F', G')`.
{F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
{N' : Type*} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N']
-- declare functions, sets, points and smoothness indices
{f f₁ : M → M'} {s s₁ t : set M} {x : M} {m n : with_top ℕ}

/-! ### Smoothness of standard maps associated to the product of manifolds -/

section prod_mk

lemma times_cont_mdiff_within_at.prod_mk {f : M → M'} {g : M → N'}
  (hf : times_cont_mdiff_within_at I I' n f s x) (hg : times_cont_mdiff_within_at I J' n g s x) :
  times_cont_mdiff_within_at I (I'.prod J') n (λ x, (f x, g x)) s x :=
begin
  rw times_cont_mdiff_within_at_iff at *,
  refine ⟨hf.1.prod hg.1, (hf.2.mono _).prod (hg.2.mono _)⟩;
  mfld_set_tac,
end

lemma times_cont_mdiff_at.prod_mk {f : M → M'} {g : M → N'}
  (hf : times_cont_mdiff_at I I' n f x) (hg : times_cont_mdiff_at I J' n g x) :
  times_cont_mdiff_at I (I'.prod J') n (λ x, (f x, g x)) x :=
hf.prod_mk hg

lemma times_cont_mdiff_on.prod_mk {f : M → M'} {g : M → N'}
  (hf : times_cont_mdiff_on I I' n f s) (hg : times_cont_mdiff_on I J' n g s) :
  times_cont_mdiff_on I (I'.prod J') n (λ x, (f x, g x)) s :=
λ x hx, (hf x hx).prod_mk (hg x hx)

lemma times_cont_mdiff.prod_mk {f : M → M'} {g : M → N'}
  (hf : times_cont_mdiff I I' n f) (hg : times_cont_mdiff I J' n g) :
  times_cont_mdiff I (I'.prod J') n (λ x, (f x, g x)) :=
λ x, (hf x).prod_mk (hg x)

lemma smooth_within_at.prod_mk {f : M → M'} {g : M → N'}
  (hf : smooth_within_at I I' f s x) (hg : smooth_within_at I J' g s x) :
  smooth_within_at I (I'.prod J') (λ x, (f x, g x)) s x :=
hf.prod_mk hg

lemma smooth_at.prod_mk {f : M → M'} {g : M → N'}
  (hf : smooth_at I I' f x) (hg : smooth_at I J' g x) :
  smooth_at I (I'.prod J') (λ x, (f x, g x)) x :=
hf.prod_mk hg

lemma smooth_on.prod_mk {f : M → M'} {g : M → N'}
  (hf : smooth_on I I' f s) (hg : smooth_on I J' g s) :
  smooth_on I (I'.prod J') (λ x, (f x, g x)) s :=
hf.prod_mk hg

lemma smooth.prod_mk {f : M → M'} {g : M → N'}
  (hf : smooth I I' f) (hg : smooth I J' g) :
  smooth I (I'.prod J') (λ x, (f x, g x)) :=
hf.prod_mk hg

end prod_mk

section projections

lemma times_cont_mdiff_within_at_fst {s : set (M × N)} {p : M × N} :
  times_cont_mdiff_within_at (I.prod J) I n prod.fst s p :=
begin
  rw times_cont_mdiff_within_at_iff,
  refine ⟨continuous_within_at_fst, _⟩,
  refine times_cont_diff_within_at_fst.congr (λ y hy, _) _,
  { simp only with mfld_simps at hy,
    simp only [hy] with mfld_simps },
  { simp only with mfld_simps }
end

lemma times_cont_mdiff_at_fst {p : M × N} :
  times_cont_mdiff_at (I.prod J) I n prod.fst p :=
times_cont_mdiff_within_at_fst

lemma times_cont_mdiff_on_fst {s : set (M × N)} :
  times_cont_mdiff_on (I.prod J) I n prod.fst s :=
λ x hx, times_cont_mdiff_within_at_fst

lemma times_cont_mdiff_fst :
  times_cont_mdiff (I.prod J) I n (@prod.fst M N) :=
λ x, times_cont_mdiff_at_fst

lemma smooth_within_at_fst {s : set (M × N)} {p : M × N} :
  smooth_within_at (I.prod J) I prod.fst s p :=
times_cont_mdiff_within_at_fst

lemma smooth_at_fst {p : M × N} :
  smooth_at (I.prod J) I prod.fst p :=
times_cont_mdiff_at_fst

lemma smooth_on_fst {s : set (M × N)} :
  smooth_on (I.prod J) I prod.fst s :=
times_cont_mdiff_on_fst

lemma smooth_fst :
  smooth (I.prod J) I (@prod.fst M N) :=
times_cont_mdiff_fst

lemma times_cont_mdiff_within_at_snd {s : set (M × N)} {p : M × N} :
  times_cont_mdiff_within_at (I.prod J) J n prod.snd s p :=
begin
  rw times_cont_mdiff_within_at_iff,
  refine ⟨continuous_within_at_snd, _⟩,
  refine times_cont_diff_within_at_snd.congr (λ y hy, _) _,
  { simp only with mfld_simps at hy,
    simp only [hy] with mfld_simps },
  { simp only with mfld_simps }
end

lemma times_cont_mdiff_at_snd {p : M × N} :
  times_cont_mdiff_at (I.prod J) J n prod.snd p :=
times_cont_mdiff_within_at_snd

lemma times_cont_mdiff_on_snd {s : set (M × N)} :
  times_cont_mdiff_on (I.prod J) J n prod.snd s :=
λ x hx, times_cont_mdiff_within_at_snd

lemma times_cont_mdiff_snd :
  times_cont_mdiff (I.prod J) J n (@prod.snd M N) :=
λ x, times_cont_mdiff_at_snd

lemma smooth_within_at_snd {s : set (M × N)} {p : M × N} :
  smooth_within_at (I.prod J) J prod.snd s p :=
times_cont_mdiff_within_at_snd

lemma smooth_at_snd {p : M × N} :
  smooth_at (I.prod J) J prod.snd p :=
times_cont_mdiff_at_snd

lemma smooth_on_snd {s : set (M × N)} :
  smooth_on (I.prod J) J prod.snd s :=
times_cont_mdiff_on_snd

lemma smooth_snd :
  smooth (I.prod J) J (@prod.snd M N) :=
times_cont_mdiff_snd

include Is I's J's

lemma smooth_iff_proj_smooth {f : M → M' × N'} :
  (smooth I (I'.prod J') f) ↔ (smooth I I' (prod.fst ∘ f)) ∧ (smooth I J' (prod.snd ∘ f)) :=
begin
  split,
  { intro h, exact ⟨smooth_fst.comp h, smooth_snd.comp h⟩ },
  { rintro ⟨h_fst, h_snd⟩, simpa only [prod.mk.eta] using h_fst.prod_mk h_snd, }
end

end projections

section prod_map

variables {g : N → N'} {r : set N} {y : N}
include Is I's Js J's

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
lemma times_cont_mdiff_within_at.prod_map' {p : M × N}
  (hf : times_cont_mdiff_within_at I I' n f s p.1) (hg : times_cont_mdiff_within_at J J' n g r p.2) :
  times_cont_mdiff_within_at (I.prod J) (I'.prod J') n (prod.map f g) (s.prod r) p :=
(hf.comp p times_cont_mdiff_within_at_fst (prod_subset_preimage_fst _ _)).prod_mk $
hg.comp p times_cont_mdiff_within_at_snd (prod_subset_preimage_snd _ _)

lemma times_cont_mdiff_within_at.prod_map
  (hf : times_cont_mdiff_within_at I I' n f s x) (hg : times_cont_mdiff_within_at J J' n g r y) :
  times_cont_mdiff_within_at (I.prod J) (I'.prod J') n (prod.map f g) (s.prod r) (x, y) :=
times_cont_mdiff_within_at.prod_map' hf hg

lemma times_cont_mdiff_at.prod_map
  (hf : times_cont_mdiff_at I I' n f x) (hg : times_cont_mdiff_at J J' n g y) :
  times_cont_mdiff_at (I.prod J) (I'.prod J') n (prod.map f g) (x, y) :=
begin
  rw ← times_cont_mdiff_within_at_univ at *,
  convert hf.prod_map hg,
  exact univ_prod_univ.symm
end

lemma times_cont_mdiff_at.prod_map' {p : M × N}
  (hf : times_cont_mdiff_at I I' n f p.1) (hg : times_cont_mdiff_at J J' n g p.2) :
  times_cont_mdiff_at (I.prod J) (I'.prod J') n (prod.map f g) p :=
begin
  rcases p,
  exact hf.prod_map hg
end

lemma times_cont_mdiff_on.prod_map
  (hf : times_cont_mdiff_on I I' n f s) (hg : times_cont_mdiff_on J J' n g r) :
  times_cont_mdiff_on (I.prod J) (I'.prod J') n (prod.map f g) (s.prod r) :=
(hf.comp times_cont_mdiff_on_fst (prod_subset_preimage_fst _ _)).prod_mk $
hg.comp (times_cont_mdiff_on_snd) (prod_subset_preimage_snd _ _)

lemma times_cont_mdiff.prod_map
  (hf : times_cont_mdiff I I' n f) (hg : times_cont_mdiff J J' n g) :
  times_cont_mdiff (I.prod J) (I'.prod J') n (prod.map f g) :=
begin
  assume p,
  exact (hf p.1).prod_map' (hg p.2)
end

lemma smooth_within_at.prod_map
  (hf : smooth_within_at I I' f s x) (hg : smooth_within_at J J' g r y) :
  smooth_within_at (I.prod J) (I'.prod J') (prod.map f g) (s.prod r) (x, y) :=
hf.prod_map hg

lemma smooth_at.prod_map
  (hf : smooth_at I I' f x) (hg : smooth_at J J' g y) :
  smooth_at (I.prod J) (I'.prod J') (prod.map f g) (x, y) :=
hf.prod_map hg

lemma smooth_on.prod_map
  (hf : smooth_on I I' f s) (hg : smooth_on J J' g r) :
  smooth_on (I.prod J) (I'.prod J') (prod.map f g) (s.prod r) :=
hf.prod_map hg

lemma smooth.prod_map
  (hf : smooth I I' f) (hg : smooth J J' g) :
  smooth (I.prod J) (I'.prod J') (prod.map f g) :=
hf.prod_map hg

end prod_map

end times_cont_mdiff

section lie_group

/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

/-!
# Lie groups
A Lie group is a group that is also a smooth manifold, in which the group operations of
multiplication and inversion are smooth maps. Smoothness of the group multiplication means that
This conversation was marked as resolved by Nicknamen
multiplication is a smooth mapping of the product manifold `G` × `G` into `G`.
Note that, since a manifold here is not second-countable and Hausdorff a Lie group here is not
guaranteed to be second-countable (even though it can be proved it is Hausdorff). Note also that Lie
groups here are not necessarily finite dimensional.
## Main definitions and statements
* `lie_add_group I G` : a Lie additive group where `G` is a manifold on the model with corners `I`.
* `lie_group I G`     : a Lie multiplicative group where `G` is a manifold on the model with
                        corners `I`.
* `lie_add_group_morphism I I' G G'`  : morphism of addittive Lie groups
* `lie_group_morphism I I' G G'`      : morphism of Lie groups
* `lie_add_group_core I G`            : allows to define a Lie additive group without first proving
                                        it is a topological additive group.
* `lie_group_core I G`                : allows to define a Lie group without first proving
                                        it is a topological group.
* `reals_lie_group`                   : real numbers are a Lie group
## Implementation notes
A priori, a Lie group here is a manifold with corners.
The definition of Lie group cannot require `I : model_with_corners 𝕜 E E` with the same space as the
model space and as the model vector space, as one might hope, beause in the product situation,
the model space is `model_prod E E'` and the model vector space is `E × E'`, which are not the same,
so the definition does not apply. Hence the definition should be more general, allowing
`I : model_with_corners 𝕜 E H`.
-/

noncomputable theory

section lie_group

set_option default_priority 100

/-- A Lie (additive) group is a group and a smooth manifold at the same time in which
the addition and negation operations are smooth. -/
class lie_add_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [add_group G] [topological_space G] [topological_add_group G] [charted_space H G]
  extends smooth_manifold_with_corners I G : Prop :=
(smooth_add : smooth (I.prod I) I (λ p : G×G, p.1 + p.2))
(smooth_neg : smooth I I (λ a:G, -a))

/-- A Lie group is a group and a smooth manifold at the same time in which
the multiplication and inverse operations are smooth. -/
@[to_additive]
class lie_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [group G] [topological_space G] [topological_group G] [charted_space H G]
  extends smooth_manifold_with_corners I G : Prop :=
(smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2))
(smooth_inv : smooth I I (λ a:G, a⁻¹))

section lie_group

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H}
{F : Type*} [normed_group F] [normed_space 𝕜 F] {J : model_with_corners 𝕜 F F}
{G : Type*} [topological_space G] [charted_space H G] [group G]
[topological_group G] [lie_group I G]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H' M] [smooth_manifold_with_corners I' M]
{E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M' : Type*} [topological_space M'] [charted_space H'' M'] [smooth_manifold_with_corners I'' M']

@[to_additive]
lemma smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2) :=
lie_group.smooth_mul

@[to_additive]
lemma smooth.mul {f : M → G} {g : M → G} (hf : smooth I' I f) (hg : smooth I' I g) :
  smooth I' I (f * g) :=
smooth_mul.comp (hf.prod_mk hg)

localized "notation `L_add` := left_add" in lie_group

localized "notation `R_add` := right_add" in lie_group

localized "notation `L` := left_mul" in lie_group

localized "notation `R` := right_mul" in lie_group

@[to_additive]
lemma smooth_left_mul {a : G} : smooth I I (left_mul a) :=
smooth_mul.comp (smooth_const.prod_mk smooth_id)

@[to_additive]
lemma smooth_right_mul {a : G} : smooth I I (right_mul a) :=
smooth_mul.comp (smooth_id.prod_mk smooth_const)

@[to_additive]
lemma smooth_on.mul {f : M → G} {g : M → G} {s : set M}
  (hf : smooth_on I' I f s) (hg : smooth_on I' I g s) :
  smooth_on I' I (f * g) s :=
(smooth_mul.comp_smooth_on (hf.prod_mk hg) : _)

lemma smooth_pow : ∀ n : ℕ, smooth I I (λ a : G, a ^ n)
| 0 := by { simp only [pow_zero], exact smooth_const }
| (k+1) := show smooth I I (λ (a : G), a * a ^ k), from smooth_id.mul (smooth_pow _)

@[to_additive]
lemma smooth_inv : smooth I I (λ x : G, x⁻¹) :=
lie_group.smooth_inv

@[to_additive]
lemma smooth.inv {f : M → G}
  (hf : smooth I' I f) : smooth I' I (λx, (f x)⁻¹) :=
smooth_inv.comp hf

@[to_additive]
lemma smooth_on.inv {f : M → G} {s : set M}
  (hf : smooth_on I' I f s) : smooth_on I' I (λx, (f x)⁻¹) s :=
smooth_inv.comp_smooth_on hf

end lie_group

section prod_lie_group

/- Instance of product group -/
@[to_additive]
instance {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]  {I : model_with_corners 𝕜 E H}
  {G : Type*} [topological_space G] [charted_space H G] [group G] [topological_group G]
  [h : lie_group I G] {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G' : Type*} [topological_space G'] [charted_space H' G']
  [group G'] [topological_group G'] [h' : lie_group I' G'] : lie_group (I.prod I') (G×G') :=
{ smooth_mul := ((smooth_fst.comp smooth_fst).smooth.mul (smooth_fst.comp smooth_snd)).prod_mk
    ((smooth_snd.comp smooth_fst).smooth.mul (smooth_snd.comp smooth_snd)),
  smooth_inv := smooth_fst.inv.prod_mk smooth_snd.inv, }

end prod_lie_group

section lie_add_group_morphism

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']

/-- Morphism of additive Lie groups. -/
structure lie_add_group_morphism (I : model_with_corners 𝕜 E E) (I' : model_with_corners 𝕜 E' E')
  (G : Type*) [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G]
  [add_group G] [topological_add_group G] [lie_add_group I G]
  (G' : Type*) [topological_space G'] [charted_space E' G'] [smooth_manifold_with_corners I' G']
  [add_group G'] [topological_add_group G'] [lie_add_group I' G'] extends add_monoid_hom G G' :=
(smooth_to_fun : smooth I I' to_fun)

/-- Morphism of Lie groups. -/
@[to_additive]
structure lie_group_morphism (I : model_with_corners 𝕜 E E) (I' : model_with_corners 𝕜 E' E')
  (G : Type*) [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G] [group G]
  [topological_group G] [lie_group I G]
  (G' : Type*) [topological_space G'] [charted_space E' G'] [smooth_manifold_with_corners I' G']
  [group G'] [topological_group G'] [lie_group I' G'] extends monoid_hom G G' :=
(smooth_to_fun : smooth I I' to_fun)

variables {I : model_with_corners 𝕜 E E} {I' : model_with_corners 𝕜 E' E'}
{G : Type*} [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G]
[group G] [topological_group G] [lie_group I G]
{G' : Type*} [topological_space G'] [charted_space E' G'] [smooth_manifold_with_corners I' G']
[group G'] [topological_group G'] [lie_group I' G']

@[to_additive]
instance : has_one (lie_group_morphism I I' G G') := ⟨⟨1, smooth_const⟩⟩
This conversation was marked as resolved by sgouezel

@[to_additive]
instance : inhabited (lie_group_morphism I I' G G') := ⟨1⟩

@[to_additive]
instance : has_coe_to_fun (lie_group_morphism I I' G G') := ⟨_, λ a, a.to_fun⟩

end lie_add_group_morphism

end lie_group

section lie_group_core

/-- Sometimes one might want to define a Lie additive group `G` without having proved previously
that `G` is a topological additive group. In such case it is possible to use `lie_add_group_core`
that does not require such instance, and then get a Lie group by invoking `to_lie_add_group`. -/
structure lie_add_group_core {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E]
  [normed_space 𝕜 E] (I : model_with_corners 𝕜 E E)
  (G : Type*) [add_group G] [topological_space G]
  [charted_space E G] [smooth_manifold_with_corners I G] : Prop :=
(smooth_add : smooth (I.prod I) I (λ p : G×G, p.1 + p.2))
(smooth_neg : smooth I I (λ a:G, -a))

/-- Sometimes one might want to define a Lie group `G` without having proved previously that `G` is
a topological group. In such case it is possible to use `lie_group_core` that does not require such
instance, and then get a Lie group by invoking `to_lie_group` defined below. -/
@[to_additive]
structure lie_group_core {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E]
  [normed_space 𝕜 E] (I : model_with_corners 𝕜 E E)
  (G : Type*) [group G] [topological_space G]
  [charted_space E G] [smooth_manifold_with_corners I G] : Prop :=
(smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2))
(smooth_inv : smooth I I (λ a:G, a⁻¹))

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E E}
{F : Type*} [normed_group F] [normed_space 𝕜 F] {J : model_with_corners 𝕜 F F}
{G : Type*} [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G] [group G]

namespace lie_group_core

variables (c : lie_group_core I G)

@[to_additive]
protected lemma to_topological_group : topological_group G :=
{ continuous_mul := c.smooth_mul.continuous,
  continuous_inv := c.smooth_inv.continuous, }

@[to_additive]
protected lemma to_lie_group : @lie_group 𝕜 _ _ _ E _ _ I G _ _ c.to_topological_group _ :=
{ smooth_mul := c.smooth_mul,
  smooth_inv := c.smooth_inv, }

end lie_group_core

end lie_group_core

/-! ### Real numbers are a Lie group -/

section real_numbers_lie_group

instance normed_group_lie_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E] :
lie_add_group (model_with_corners_self 𝕜 E) E :=
{ smooth_add :=
  begin
    rw smooth_iff,
    refine ⟨continuous_add, λ x y, _⟩,
    simp only [prod.mk.eta] with mfld_simps,
    rw times_cont_diff_on_univ,
    exact times_cont_diff_add,
  end,
  smooth_neg :=
  begin
    rw smooth_iff,
    refine ⟨continuous_neg, λ x y, _⟩,
    simp only [prod.mk.eta] with mfld_simps,
    rw times_cont_diff_on_univ,
    exact times_cont_diff_neg,
  end }

instance reals_lie_group : lie_add_group (model_with_corners_self ℝ ℝ) ℝ := by apply_instance

end real_numbers_lie_group

end lie_group



end CMP_2020
