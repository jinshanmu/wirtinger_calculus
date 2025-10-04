import Mathlib

/-!
  # Wirtinger split with PDF-style symbols (safe identifiers)

  Notation follows the PDF:
  - `J_H`, `J_W` are the complex-structure maps (multiplication by `i`) as `ℝ`-linear maps.
  - For an `ℝ`-linear map `T : H →ₗ[ℝ] W`:
        𝒜 T := J_W ∘ T ∘ J_H
        Tplus  := (1/2) • (T - 𝒜 T)
        Tminus := (1/2) • (T + 𝒜 T)
    and we prove `T = Tplus + Tminus`.
-/

noncomputable section
open Complex

namespace Wirtinger

variable {H W : Type*}
variable [AddCommGroup H] [Module ℂ H]
variable [AddCommGroup W] [Module ℂ W]

/-- `J_H`: multiplication by `I` on `H` as an `ℝ`-linear map. -/
@[simp] def J_H : H →ₗ[ℝ] H where
  toFun := fun v => (I : ℂ) • v
  map_add' := by
    intro v w; simp [smul_add]
  map_smul' := by
    intro r v
    -- real and complex scalars commute on complex vector spaces
    simpa using (smul_comm (r : ℝ) (I : ℂ) v).symm

/-- `J_W`: multiplication by `I` on `W` as an `ℝ`-linear map. -/
@[simp] def J_W : W →ₗ[ℝ] W where
  toFun := fun w => (I : ℂ) • w
  map_add' := by
    intro x y; simp [smul_add]
  map_smul' := by
    intro r w
    simpa using (smul_comm (r : ℝ) (I : ℂ) w).symm

/-- Abbreviation `𝒜 T = J_W ∘ T ∘ J_H`. -/
@[simp] def 𝒜 (T : H →ₗ[ℝ] W) : H →ₗ[ℝ] W :=
  (J_W).comp (T.comp (J_H))

/-- Pointwise form of `𝒜`. This is definitionally true, handy for `simp`. -/
@[simp] lemma 𝒜_apply (T : H →ₗ[ℝ] W) (v : H) : 𝒜 T v = (I : ℂ) • T ((I : ℂ) • v) := rfl

/-- Plus (complex-linear) part: `Tplus = (1/2) • (T - 𝒜 T)`. -/
@[simp] def Tplus (T : H →ₗ[ℝ] W) : H →ₗ[ℝ] W :=
  ((1/2 : ℝ)) • (T - 𝒜 T)

/-- Minus (conjugate-linear) part: `Tminus = (1/2) • (T + 𝒜 T)`. -/
@[simp] def Tminus (T : H →ₗ[ℝ] W) : H →ₗ[ℝ] W :=
  ((1/2 : ℝ)) • (T + 𝒜 T)

/-- Wirtinger split: `T = Tplus + Tminus` as `ℝ`-linear maps. -/
@[simp] lemma plus_add_minus (T : H →ₗ[ℝ] W) : Tplus T + Tminus T = T := by
  ext v
  calc
    (Tplus T + Tminus T) v
        = (1/2 : ℝ) • (T v - (𝒜 T) v)
          + (1/2 : ℝ) • (T v + (𝒜 T) v) := by
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

end Wirtinger
