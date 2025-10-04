import Mathlib

/-!
# Basic.lean — Setup & Notation (single-namespace)

This file provides:

* Complex structure `J` as an `ℝ`-linear map (multiplication by `i`)
* Shorthands `J_H`, `J_W`
* Sandwich `𝒜 T = J_W ∘ T ∘ J_H`
* Wirtinger split on `ℝ`-linear maps: `Tplus`, `Tminus`, and the split lemma
* Predicates `IsCLinearR` / `IsALinearR`
* Hermitian adjoint notation `†` for complex continuous linear maps
* Abstract `Conjugation`
* Hermitian adjoint for a conjugate-linear (anti-linear) map

Conventions (mathlib): the inner product is conjugate-linear in the first slot
and linear in the second slot.
-/

noncomputable section
open Complex

namespace Wirtinger

universe u v
variable {H : Type u} {W : Type v}
variable [AddCommGroup H] [Module ℂ H]
variable [AddCommGroup W] [Module ℂ W]

/-! ## Complex structure as an ℝ-linear map: `J` -/

/-- Multiplication by `i` on `V` as an `ℝ`-linear map. -/
@[simp] def J (V : Type _) [AddCommGroup V] [Module ℂ V] : V →ₗ[ℝ] V where
  toFun := fun v => (I : ℂ) • v
  map_add' := by intro v w; simp [smul_add]
  map_smul' := by
    intro r v
    -- real and complex scalars commute on a complex vector space
    simpa using (smul_comm (r : ℝ) (I : ℂ) v).symm

@[simp] lemma J_apply {V} [AddCommGroup V] [Module ℂ V] (v : V) :
    J V v = (I : ℂ) • v := rfl

/-- `J ∘ J = - id` as `ℝ`-linear maps. -/
lemma J_comp_J (V : Type _) [AddCommGroup V] [Module ℂ V] :
    (J V).comp (J V) = - LinearMap.id := by
  ext v; simp [J, smul_smul, Complex.I_mul_I]

/-- PDF-style shorthands. -/
abbrev J_H : H →ₗ[ℝ] H := J H
abbrev J_W : W →ₗ[ℝ] W := J W

/-! ## Sandwich and Wirtinger split on ℝ-linear maps -/

/-- Sandwich operator: `𝒜 T = J_W ∘ T ∘ J_H`. -/
@[simp] def 𝒜 (T : H →ₗ[ℝ] W) : H →ₗ[ℝ] W :=
  (J_W).comp (T.comp J_H)

@[simp] lemma 𝒜_apply (T : H →ₗ[ℝ] W) (v : H) :
    𝒜 T v = (I : ℂ) • T ((I : ℂ) • v) := rfl

/-- Plus (complex-linear) part: `Tplus = (1/2) • (T - 𝒜 T)`. -/
@[simp] def Tplus (T : H →ₗ[ℝ] W) : H →ₗ[ℝ] W :=
  ((1/2 : ℝ)) • (T - 𝒜 T)

/-- Minus (conjugate-linear) part: `Tminus = (1/2) • (T + 𝒜 T)`. -/
@[simp] def Tminus (T : H →ₗ[ℝ] W) : H →ₗ[ℝ] W :=
  ((1/2 : ℝ)) • (T + 𝒜 T)

/-- Split identity: `T = Tplus + Tminus`. -/
@[simp] lemma plus_add_minus (T : H →ₗ[ℝ] W) :
    Tplus T + Tminus T = T := by
  ext v
  calc
    (Tplus T + Tminus T) v
        = (1/2 : ℝ) • (T v - (𝒜 T) v) + (1/2 : ℝ) • (T v + (𝒜 T) v) := by
          simp [Tplus, Tminus, 𝒜, sub_eq_add_neg]
    _ = ((1/2 : ℝ) • T v + (1/2 : ℝ) • T v)
        + ((1/2 : ℝ) • (-(𝒜 T) v) + (1/2 : ℝ) • ((𝒜 T) v)) := by
          simp [smul_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, smul_neg]
    _ = ((1/2 : ℝ) + (1/2 : ℝ)) • T v + 0 := by
          simp [add_smul, smul_neg]
    _ = (1 : ℝ) • T v := by
          norm_num
    _ = T v := by
          simp

/-! ## Complex- and conjugate-linearity via `J` (as predicates) -/

/-- A real-linear `T` is complex-linear iff it commutes with `J`. -/
def IsCLinearR (T : H →ₗ[ℝ] W) : Prop :=
  (J_W).comp T = T.comp J_H

/-- A real-linear `T` is conjugate-linear iff it anti-commutes with `J`. -/
def IsALinearR (T : H →ₗ[ℝ] W) : Prop :=
  (J_W).comp T = - (T.comp J_H)

/-! ## Hermitian adjoint notation for complex continuous linear maps -/

notation A "†" => ContinuousLinearMap.adjoint A
-- For `A : H →L[ℂ] W` (with inner-product instances),
-- mathlib supplies:  ⟪A x, y⟫ = ⟪x, A† y⟫  and  A†† = A.

/-! ## Conjugations (abstract) -/

/-- A conjugation on a complex vector space:
    an `ℝ`-linear involution that anti-commutes with `J`. -/
structure Conjugation (V : Type _) [AddCommGroup V] [Module ℂ V] where
  C : V →ₗ[ℝ] V
  involutive : C.comp C = LinearMap.id
  antiJ : C.comp (J V) = - (J V).comp C

section
variable {V : Type _} [AddCommGroup V] [Module ℂ V]

@[simp] lemma Conjugation.comp_self_id (C : Conjugation V) :
    C.C.comp C.C = LinearMap.id := C.involutive

/-- Pointwise form of `C ∘ J = - J ∘ C`. -/
@[simp] lemma Conjugation.antiJ_apply (C : Conjugation V) (v : V) :
    C.C ((I : ℂ) • v) = - (I : ℂ) • C.C v := by
  have := congrArg (fun (L : V →ₗ[ℝ] V) => L v) C.antiJ
  simpa [LinearMap.comp_apply, J, smul_smul] using this
end

/-! ## Conjugate-linear (anti-linear) maps packaged as `ℝ`-linear with `antiJ` -/

/-- An anti-linear (conjugate-linear) map packaged as an `ℝ`-linear map that
    anti-commutes with the complex structures. -/
structure ALinear
  (H : Type u) (W : Type v)
  [AddCommGroup H] [Module ℂ H]
  [AddCommGroup W] [Module ℂ W] where
  toLinear : H →ₗ[ℝ] W
  antiJ : (J W).comp toLinear = - toLinear.comp (J H)

namespace ALinear

@[simp] lemma antiJ_apply
  {H : Type u} {W : Type v}
  [AddCommGroup H] [Module ℂ H]
  [AddCommGroup W] [Module ℂ W]
  (T : ALinear H W) (v : H) :
  (I : ℂ) • T.toLinear v = - T.toLinear ((I : ℂ) • v) := by
  have := congrArg (fun (L : H →ₗ[ℝ] W) => L v) T.antiJ
  simpa [LinearMap.comp_apply, J, smul_smul] using this

/-- `ALinear` implies the earlier predicate `IsALinearR`. -/
lemma isALinearR
  {H : Type u} {W : Type v}
  [AddCommGroup H] [Module ℂ H]
  [AddCommGroup W] [Module ℂ W]
  (T : ALinear H W) :
  IsALinearR (T := T.toLinear) := T.antiJ

end ALinear

end Wirtinger

/-!
## Hermitian adjoint for a conjugate-linear map

Conventions (mathlib): `inner` is conjugate-linear in the 1st slot, linear in the 2nd.
We build `(conjAdjoint B) : F → E` and prove:

* `inner ((conjAdjoint B) x) y = inner (B y) x`
* `inner x (B y) = star (inner ((conjAdjoint B) x) y)`
-/

namespace ConjAdj

/-- For fixed `x : F`, the bounded linear functional `y ↦ inner (B y) x`. -/
private def phi
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (B : E → F)
  (h_add : ∀ y z, B (y + z) = B y + B z)
  (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
  (h_cont : Continuous B)
  (x : F) : E →L[ℂ] ℂ :=
by
  classical
  -- 1) Underlying linear map (linear in y since B is conjugate-linear):
  let L : E →ₗ[ℂ] ℂ :=
  { toFun := fun y => inner (𝕜 := ℂ) (B y) x
  , map_add' := by
      intro y z
      simp [h_add y z]
  , map_smul' := by
      intro a y
      -- B (a•y) = star a • B y; first slot conjugate-linear:
      -- inner ((star a) • B y) x = a * inner (B y) x
      simp [h_smul a y, mul_comm] }
  -- 2) Continuity: y ↦ inner (B y) x = star (inner x (B y))
  have hx : Continuous fun w : F =>
      ((InnerProductSpace.toDual ℂ F) x) w :=
    ((InnerProductSpace.toDual ℂ F) x).continuous
  have hcomp : Continuous fun y : E =>
      ((InnerProductSpace.toDual ℂ F) x) (B y) := hx.comp h_cont
  have hstar : Continuous fun y : E =>
      star (inner (𝕜 := ℂ) x (B y)) :=
    continuous_star.comp hcomp
  have hLcont : Continuous fun y : E => L y := by
    -- Convert `hstar` to the goal using conjugate symmetry.
    convert hstar using 1
    ext y; simp [L]
  -- 3) Package:
  exact { toLinearMap := L, cont := hLcont }

/-- Adjoint of a conjugate-linear `B`, via the Riesz isometry. -/
def conjAdjoint
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (B : E → F)
  (h_add : ∀ y z, B (y + z) = B y + B z)
  (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
  (h_cont : Continuous B) :
  F → E :=
fun x => (InnerProductSpace.toDual ℂ E).symm (phi B h_add h_smul h_cont x)

/-- Riesz characterization for the conjugate-linear adjoint:
`inner ((conjAdjoint B) x) y = inner (B y) x`. -/
lemma inner_conjAdjoint
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (B : E → F)
  (h_add : ∀ y z, B (y + z) = B y + B z)
  (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
  (h_cont : Continuous B)
  (x : F) (y : E) :
  inner (𝕜 := ℂ) ((conjAdjoint B h_add h_smul h_cont) x) y
  = inner (𝕜 := ℂ) (B y) x :=
by
  classical
  change
    (InnerProductSpace.toDual ℂ E) ((conjAdjoint B h_add h_smul h_cont) x) y
    = inner (𝕜 := ℂ) (B y) x
  simp [conjAdjoint, phi]

/-- Formal adjoint identity:
`inner x (B y) = star (inner ((conjAdjoint B) x) y)`. -/
lemma inner_eq_star_adjoint
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (B : E → F)
  (h_add : ∀ y z, B (y + z) = B y + B z)
  (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
  (h_cont : Continuous B)
  (x : F) (y : E) :
  inner (𝕜 := ℂ) x (B y) =
  star (inner (𝕜 := ℂ) ((conjAdjoint B h_add h_smul h_cont) x) y) :=
by
  classical
  have h := inner_conjAdjoint B h_add h_smul h_cont x y
  -- Take star and use conjugate symmetry:
  simpa [inner_conj_symm] using (congrArg star h).symm

end ConjAdj
