-- FILE: WirtingerCalculus/Differential.lean
import Mathlib
import WirtingerCalculus.Basic

/-!
# Differential.lean — Real Fréchet derivative and Wirtinger split

We formalize the real Fréchet derivative on complex Banach spaces and the
Wirtinger split of the derivative.

Main defs:
* `HasRDerivAt f u D`  : real Fréchet derivative (aka `HasFDerivAt` over `ℝ`).
* `fderivR f u`        : the derivative `H →L[ℝ] W`.
* `Jc`                 : `J` (multiply by `I`) as a *continuous* `ℝ`-linear map.
* `Aℒ`                 : sandwich on `H →L[ℝ] W`, `Aℒ T = Jc_W ∘ T ∘ Jc_H`.
* `DplusCLM/DminusCLM` : Wirtinger split of `fderivR f u`.

Key lemmas:
* `Aℒ_involutive : Aℒ (Aℒ T) = T`.
* `Dplus_add_Dminus : DplusCLM f u + DminusCLM f u = fderivR f u`.
* `isCLinearR_Dplus` / `isALinearR_Dminus` — (anti)commutation with `Jc`.
-/

noncomputable section
open Complex

namespace Wirtinger

universe u v

variable {H : Type u} {W : Type v}
variable [AddCommGroup H] [Module ℂ H]
variable [AddCommGroup W] [Module ℂ W]
variable [SeminormedAddCommGroup H] [SeminormedAddCommGroup W]
variable [NormedSpace ℂ H] [NormedSpace ℂ W]
-- Keep the real structures explicit for `→L[ℝ]`.
variable [NormedSpace ℝ H] [NormedSpace ℝ W]

/-! ## Real Fréchet derivative -/

abbrev HasRDerivAt (f : H → W) (u : H) (D : H →L[ℝ] W) : Prop :=
  HasFDerivAt f D u

@[simp] abbrev fderivR (f : H → W) (u : H) : H →L[ℝ] W :=
  fderiv ℝ f u

/-! ## `J` as a continuous `ℝ`-linear map -/

/-- `Jc V` is multiplication by `I` as a *continuous* `ℝ`-linear map. -/
def Jc (V : Type _) [AddCommGroup V] [Module ℂ V]
    [SeminormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] : V →L[ℝ] V :=
by
  classical
  -- Use a uniform bound: ‖I • v‖ = ‖I‖ ‖v‖ = 1⋅‖v‖
  refine (J V).continuous_of_bound (1 : ℝ) ?_
  intro v
  have hI : ‖(I : ℂ)‖ = 1 := by simpa using norm_I
  -- from equality to ≤ 1⋅‖v‖
  simpa [J, hI, one_mul] using (le_of_eq (norm_smul (I : ℂ) v))

@[simp] lemma Jc_apply {V} [AddCommGroup V] [Module ℂ V]
    [SeminormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    (v : V) : Jc V v = (I : ℂ) • v := rfl

/-- Pointwise form of `Jc ∘ Jc = -id`. -/
@[simp] lemma Jc_comp_Jc_apply (V : Type _) [AddCommGroup V] [Module ℂ V]
    [SeminormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    (v : V) :
    ((Jc V).comp (Jc V)) v = - v := by
  -- (I • (I • v)) = (I*I) • v = (-1 : ℂ) • v; as a vector, that *is* `-v`
  simpa [Jc, smul_smul, Complex.I_mul_I, neg_one_smul]

/-! ## Sandwich on continuous `ℝ`-linear maps -/

/-- Sandwich operator on `H →L[ℝ] W`: `Aℒ T = Jc_W ∘ T ∘ Jc_H`. -/
@[simp] def Aℒ (T : H →L[ℝ] W) : H →L[ℝ] W :=
  (Jc_W).comp (T.comp Jc_H)

@[simp] lemma Aℒ_apply (T : H →L[ℝ] W) (v : H) :
    Aℒ (H:=H) (W:=W) T v = (I : ℂ) • T ((I : ℂ) • v) := rfl

/-- `Aℒ` is an involution: `Aℒ (Aℒ T) = T`. -/
lemma Aℒ_involutive (T : H →L[ℝ] W) :
    Aℒ (H:=H) (W:=W) (Aℒ T) = T := by
  -- Prove pointwise to avoid any version-fragile algebra lemmas.
  ext v
  -- expand both `Aℒ` layers
  simp [Aℒ, Jc_apply, smul_smul, Complex.I_mul_I]
  -- At this point the goal is `(-1 : ℂ) • T ((-1 : ℂ) • v) = T v`.
  -- Replace the inner `(-1 : ℂ) • v` by `-v` and use real-linearity of `T`.
  have h_inner : ((-1 : ℂ) : ℂ) • v = -v := by
    simpa [neg_one_smul]
  have hT : T ((-1 : ℂ) • v) = - T v := by
    -- since `(-1 : ℂ) • v = -v`, this is just `T (-v) = - T v`.
    simpa [h_inner] using (T.map_neg v)
  simpa [hT, neg_one_smul]

/-! ## Wirtinger split of the real Fréchet derivative -/

/-- Plus (complex-linear) part. -/
def DplusCLM (f : H → W) (u : H) : H →L[ℝ] W :=
  ((1/2 : ℝ)) • (fderivR f u - Aℒ (fderivR f u))

/-- Minus (conjugate-linear) part. -/
def DminusCLM (f : H → W) (u : H) : H →L[ℝ] W :=
  ((1/2 : ℝ)) • (fderivR f u + Aℒ (fderivR f u))

/-- Split identity: `Df = Dplus + Dminus`. -/
lemma Dplus_add_Dminus (f : H → W) (u : H) :
    DplusCLM (H:=H) (W:=W) f u + DminusCLM f u = fderivR f u := by
  ext v
  simp [DplusCLM, DminusCLM, Aℒ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        smul_add, add_smul, smul_neg]
  norm_num

/-! ## (Anti)commutation with `Jc` (direction linearity) -/

/-- `Dplus` commutes with `Jc`: complex-linear in the direction. -/
lemma isCLinearR_Dplus (f : H → W) (u : H) :
    (Jc_W).comp (DplusCLM f u) = (DplusCLM f u).comp (Jc_H) := by
  ext v
  simp [DplusCLM, Aℒ, sub_eq_add_neg, smul_add, add_comm, add_left_comm, add_assoc]

/-- `Dminus` anti-commutes with `Jc`: conjugate-linear in the direction. -/
lemma isALinearR_Dminus (f : H → W) (u : H) :
    (Jc_W).comp (DminusCLM f u) = - (DminusCLM f u).comp (Jc_H) := by
  ext v
  simp [DminusCLM, Aℒ, sub_eq_add_neg, smul_add, add_comm, add_left_comm, add_assoc]

/-- Pointwise decomposition of the real Gâteaux derivative. -/
lemma fderivR_apply_split (f : H → W) (u v : H) :
    fderivR f u v = DplusCLM f u v + DminusCLM f u v := by
  simpa using
    congrArg (fun (T : H →L[ℝ] W) => T v) (Dplus_add_Dminus (H:=H) (W:=W) f u)

end Wirtinger
