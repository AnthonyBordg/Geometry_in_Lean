import topology.algebra.continuous_functions

namespace CMP_2020

/-!
# Continuous bundled map
In this file we define the type `continuous_map` of continuous bundled maps.
-/

/-- Bundled continuous maps. -/
@[protect_proj]
structure continuous_map (α : Type*) (β : Type*)
[topological_space α] [topological_space β] :=
(to_fun             : α → β)
(continuous_to_fun  : continuous to_fun)

/- notation `C(` α `, ` β `)` := continuous_map α β -/

namespace continuous_map

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

/-instance : has_coe_to_fun (C(α, β)) := ⟨_, continuous_map.to_fun⟩-/

variables {α β} {f g : continuous_map α β}

/-@[ext] theorem ext (H : ∀ x : α, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H-/

instance [inhabited β] : inhabited C(α, β) :=
⟨⟨λ _, default _, continuous_const⟩⟩

protected lemma continuous (f : C(α, β)) : continuous f := f.continuous_to_fun

/-- Takes `b` in input and gives the continuous bundled function constantly valued `b` in output. -/
def const (b : β) : C(α, β) := ⟨λ x, b, continuous_const⟩

end continuous_map

namespace continuous_map

@[to_additive]
instance has_mul {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [has_mul β] [has_continuous_mul β] : has_mul C(α, β) :=
⟨λ f g, ⟨f * g, continuous_mul.comp (f.continuous.prod_mk g.continuous)⟩⟩

@[to_additive]
instance {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [has_one β] : has_one C(α, β) := ⟨const (1 : β)⟩

end continuous_map

section continuous_map

@[to_additive continuous_map_add_semigroup]
instance continuous_map_semigroup {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [semigroup β] [has_continuous_mul β] : semigroup C(α, β) :=
{ mul_assoc := λ a b c, by ext; exact mul_assoc _ _ _,
  ..continuous_map.has_mul}

@[to_additive continuous_map_add_monoid]
instance continuous_map_monoid {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [monoid β] [has_continuous_mul β] : monoid C(α, β) :=
{ one_mul := λ a, by ext; exact one_mul _,
  mul_one := λ a, by ext; exact mul_one _,
  ..continuous_map_semigroup,
  ..continuous_map.has_one }

@[to_additive continuous_map_add_comm_monoid]
instance continuous_map_comm_monoid {α : Type*} {β : Type*} [topological_space α]
[topological_space β] [comm_monoid β] [has_continuous_mul β] : comm_monoid C(α, β) :=
{ one_mul := λ a, by ext; exact one_mul _,
  mul_one := λ a, by ext; exact mul_one _,
  mul_comm := λ a b, by ext; exact mul_comm _ _,
  ..continuous_map_semigroup,
  ..continuous_map.has_one }

@[to_additive continuous_map_add_group]
instance continuous_map_group {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [group β] [topological_group β] : group C(α, β) :=
{ inv := λ f, ⟨λ x, (f x)⁻¹, continuous_inv.comp f.continuous⟩,
  mul_left_inv := λ a, by ext; exact mul_left_inv _,
  ..continuous_map_monoid }

@[to_additive continuous_map_add_comm_group]
instance continuous_map_comm_group {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [comm_group β] [topological_group β] : comm_group C(α, β) :=
{ ..continuous_map_group,
  ..continuous_map_comm_monoid }

end continuous_map

section continuous_map

instance continuous_map_semiring {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [semiring β] [topological_semiring β] : semiring C(α, β) :=
{ left_distrib := λ a b c, by ext; exact left_distrib _ _ _,
  right_distrib := λ a b c, by ext; exact right_distrib _ _ _,
  zero_mul := λ a, by ext; exact zero_mul _,
  mul_zero := λ a, by ext; exact mul_zero _,
  ..continuous_map_add_comm_monoid,
  ..continuous_map_monoid }

instance continuous_map_ring {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  [ring β] [topological_ring β] : ring C(α, β) :=
{ ..continuous_map_semiring,
  ..continuous_map_add_comm_group, }

instance continuous_map_comm_ring {α : Type*} {β : Type*} [topological_space α]
[topological_space β] [comm_ring β] [topological_ring β] : comm_ring C(α, β) :=
{ ..continuous_map_semiring,
  ..continuous_map_add_comm_group,
  ..continuous_map_comm_monoid,}

end continuous_map

section continuous_map

instance continuous_map_has_scalar {α : Type*} [topological_space α]
  (R : Type*) [semiring R] [topological_space R]
  (M : Type*) [topological_space M] [add_comm_monoid M]
  [semimodule R M] [topological_semimodule R M] :
  has_scalar R C(α, M) :=
⟨λ r f, ⟨r • f, continuous_const.smul f.continuous⟩⟩

instance continuous_map_semimodule {α : Type*} [topological_space α]
{R : Type*} [semiring R] [topological_space R]
{M : Type*} [topological_space M] [add_comm_group M] [topological_add_group M]
[semimodule R M] [topological_semimodule R M] :
  semimodule R C(α, M) :=
  semimodule.of_core $
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add c (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul c₁ c₂ (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul c₁ c₂ (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x) }

end continuous_map

section continuous_map

variables {α : Type*} [topological_space α]
{R : Type*} [comm_semiring R]
{A : Type*} [topological_space A] [semiring A]
[algebra R A] [topological_semiring A]

/-- Continuous constant functions as a `ring_hom`. -/
def continuous_map.C : R →+* C(α, A) :=
{ to_fun    := λ c : R, ⟨λ x: α, ((algebra_map R A) c), continuous_const⟩,
  map_one'  := by ext x; exact (algebra_map R A).map_one,
  map_mul'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_mul _ _,
  map_zero' := by ext x; exact (algebra_map R A).map_zero,
  map_add'  := λ c₁ c₂, by ext x; exact (algebra_map R A).map_add _ _ }

variables [topological_space R] [topological_semimodule R A]

instance : algebra R C(α, A) :=
{ to_ring_hom := continuous_map.C,
  commutes' := λ c f, by ext x; exact algebra.commutes' _ _,
  smul_def' := λ c f, by ext x; exact algebra.smul_def' _ _,
  ..continuous_map_semiring }

end continuous_map

section continuous_map

instance continuous_map_has_scalar' {α : Type*} [topological_space α]
  {R : Type*} [semiring R] [topological_space R]
  {M : Type*} [topological_space M] [add_comm_group M]
  [semimodule R M] [topological_semimodule R M] :
  has_scalar C(α, R) C(α, M) :=
⟨λ f g, ⟨λ x, (f x) • (g x), (continuous.smul f.2 g.2)⟩⟩

instance continuous_map_module' {α : Type*} [topological_space α]
  (R : Type*) [ring R] [topological_space R] [topological_ring R]
  (M : Type*) [topological_space M] [add_comm_group M] [topological_add_group M]
  [module R M] [topological_module R M]
  : module C(α, R) C(α, M) :=
  semimodule.of_core $
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add (c x) (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul (c₁ x) (c₂ x) (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul (c₁ x) (c₂ x) (f x),
  one_smul := λ f, by ext x; exact one_smul R (f x) }

end continuous_map

end CMP_2020
