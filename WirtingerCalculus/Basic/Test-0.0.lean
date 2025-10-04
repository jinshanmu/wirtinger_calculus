import Mathlib

/-!
  Basic0.lean — Wirtinger split

  This file defines the Wirtinger projections of a real-linear map
  `T : E →ₗ[ℝ] F` into its complex-linear and conjugate-linear parts:

    `clPart T := (1/2) • (T - J_F ∘ T ∘ J_E)`
    `alPart T := (1/2) • (T + J_F ∘ T ∘ J_E)`

  and proves the decomposition  `T = clPart T + alPart T`.

-/

noncomputable section
open Complex

namespace Wirtinger

variable {E F : Type*}
variable [AddCommGroup E] [Module ℂ E]
variable [AddCommGroup F] [Module ℂ F]

/-- Multiplication by `I` on a complex vector space `E`, as an `ℝ`-linear map. -/
@[simp] def J (E : Type*) [AddCommGroup E] [Module ℂ E] : E →ₗ[ℝ] E where
  toFun := fun v => (I : ℂ) • v
  map_add' := by
    intro v w; simp [smul_add]
  map_smul' := by
    intro r v
    -- `r : ℝ`. Scalars `ℝ` and `ℂ` commute on a complex vector space.
    -- `smul_comm` gives: r • (I • v) = I • (r • v).
    -- We need the symmetric direction.
    simpa using (smul_comm (r : ℝ) (I : ℂ) v).symm

/-- Abbreviation used in formulas: `A T = J_F ∘ T ∘ J_E`. -/
@[simp] def A (T : E →ₗ[ℝ] F) : E →ₗ[ℝ] F :=
  (J F).comp (T.comp (J E))

/-- Complex-linear ("plus") part of a real-linear map `T`. -/
@[simp] def clPart (T : E →ₗ[ℝ] F) : E →ₗ[ℝ] F :=
  ((1/2 : ℝ)) • (T - A (E:=E) (F:=F) T)

/-- Conjugate-linear ("minus") part of a real-linear map `T`. -/
@[simp] def alPart (T : E →ₗ[ℝ] F) : E →ₗ[ℝ] F :=
  ((1/2 : ℝ)) • (T + A (E:=E) (F:=F) T)

/-- Wirtinger split: `T = clPart T + alPart T` as `ℝ`-linear maps. -/
@[simp] lemma cl_add_al (T : E →ₗ[ℝ] F) :
    clPart (E:=E) (F:=F) T + alPart (E:=E) (F:=F) T = T := by
  ext v
  calc
    (clPart (E:=E) (F:=F) T + alPart (E:=E) (F:=F) T) v
        = (1/2 : ℝ) • (T v - (A (E:=E) (F:=F) T) v)
          + (1/2 : ℝ) • (T v + (A (E:=E) (F:=F) T) v) := by
            simp [clPart, alPart, A, sub_eq_add_neg]
    _ = ((1/2 : ℝ) • T v + (1/2 : ℝ) • T v)
          + ((1/2 : ℝ) • (-(A (E:=E) (F:=F) T) v) + (1/2 : ℝ) • ((A (E:=E) (F:=F) T) v)) := by
            simp [smul_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, smul_neg]
    _ = ((1/2 : ℝ) + (1/2 : ℝ)) • T v + 0 := by
      simp [add_smul, smul_neg]
    _ = (1 : ℝ) • T v := by
      norm_num
    _ = T v := by
      simp

end Wirtinger
