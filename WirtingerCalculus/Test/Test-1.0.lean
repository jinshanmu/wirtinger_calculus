import Mathlib
import WirtingerCalculus.Basic

/-!
# Differential.lean — Real Fréchet derivative and Wirtinger split

This file formalizes the "Setup and Notation" section for first-order (real) Fréchet
calculus on complex Hilbert spaces and introduces the Wirtinger split of the real
Fréchet derivative.

Main definitions
* `HasRDerivAt f u D` : real Fréchet derivative (alias of `HasFDerivAt` over `ℝ`).
* `fderivR f u`       : the real Fréchet derivative `H →L[ℝ] W` at `u`.
* `Jc`                : `J` as a *continuous* `ℝ`-linear map.
* `Aℒ`                : sandwich operator on continuous maps, `Aℒ T = Jc_W ∘ T ∘ Jc_H`.
* `DplusCLM / DminusCLM` : Wirtinger split of `fderivR f u` on `H →L[ℝ] W`.

Main lemmas
* `Aℒ_involutive`     : `Aℒ (Aℒ T) = T`.
* `Dplus_add_Dminus`  : `DplusCLM f u + DminusCLM f u = fderivR f u`.
* `isCLinearR_Dplus`  : `DplusCLM` commutes with `Jc` (complex-linear in the direction).
* `isALinearR_Dminus` : `DminusCLM` anti-commutes with `Jc` (conjugate-linear in the direction).

These correspond to (2.1)–(2.4) in the LaTeX text: the real Fréchet derivative,
Wirtinger operators, linearity properties, and the decomposition.
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
-- Real scalar structure (restriction of scalars is available by typeclass inference,
-- but we keep these explicit for clarity in `fderiv ℝ`).
variable [NormedSpace ℝ H] [NormedSpace ℝ W]

/-! ## Real Fréchet derivative on complex spaces -/

/-- Real Fréchet differentiability of `f : H → W` at `u` with derivative `D`
(as `H →L[ℝ] W`). This is just `HasFDerivAt` with base field `ℝ`. -/
abbrev HasRDerivAt (f : H → W) (u : H) (D : H →L[ℝ] W) : Prop :=
  HasFDerivAt f D u

/-- The real Fréchet derivative (as a continuous `ℝ`-linear map). -/
@[simp] abbrev fderivR (f : H → W) (u : H) : H →L[ℝ] W :=
  fderiv ℝ f u

/-! ## `J` as a *continuous* `ℝ`-linear map -/

/-- `Jc V` is multiplication by `I` as a *continuous* `ℝ`-linear map. -/
@[simp] def Jc (V : Type _) [AddCommGroup V] [Module ℂ V]
    [SeminormedAddCommGroup V] [NormedSpace ℂ V] : V →L[ℝ] V :=
by
  classical
  refine { toLinearMap := J V
         , cont := ?_ } ;
  -- continuity: `v ↦ I • v` is continuous
  refine Continuous_iff_continuousAt.mpr (fun _ => ?_)
  simpa using (ContinuousAt.const_smul (c := (I : ℂ)) continuousAt_id)

@[simp] lemma Jc_apply {V} [AddCommGroup V] [Module ℂ V]
    [SeminormedAddCommGroup V] [NormedSpace ℂ V]
    (v : V) : Jc V v = (I : ℂ) • v := rfl

/-- `Jc ∘ Jc = - id` for continuous maps. -/
@[simp] lemma Jc_comp_Jc (V : Type _) [AddCommGroup V] [Module ℂ V]
    [SeminormedAddCommGroup V] [NormedSpace ℂ V] :
    (Jc V).comp (Jc V) = - (ContinuousLinearMap.id ℝ V) := by
  ext v; simp [Jc, smul_smul, Complex.I_mul_I]

@[simp] abbrev Jc_H : H →L[ℝ] H := Jc H
@[simp] abbrev Jc_W : W →L[ℝ] W := Jc W

/-! ## Sandwich on continuous `ℝ`-linear maps -/

/-- Sandwich operator on `H →L[ℝ] W`: `Aℒ T = Jc_W ∘ T ∘ Jc_H`. -/
@[simp] def Aℒ (T : H →L[ℝ] W) : H →L[ℝ] W :=
  (Jc_W).comp (T.comp Jc_H)

@[simp] lemma Aℒ_apply (T : H →L[ℝ] W) (v : H) :
    Aℒ (H:=H) (W:=W) T v = (I : ℂ) • T ((I : ℂ) • v) := rfl

/-- `𝒜` is an involution at the continuous level: `Aℒ (Aℒ T) = T`. -/
@[simp] lemma Aℒ_involutive (T : H →L[ℝ] W) :
    Aℒ (H:=H) (W:=W) (Aℒ T) = T := by
  -- `Aℒ T = Jc_W ∘ T ∘ Jc_H`; composing twice yields
  -- `(Jc_W ∘ Jc_W) ∘ T ∘ (Jc_H ∘ Jc_H) = (-id) ∘ T ∘ (-id) = T`.
  ext v
  simp [Aℒ, Jc_comp_Jc, ContinuousLinearMap.comp_apply, LinearMap.comp_apply, smul_smul]

/-! ## Wirtinger split of the real Fréchet derivative -/

/-- Plus (complex-linear) part of the real derivative. -/
@[simp] def DplusCLM (f : H → W) (u : H) : H →L[ℝ] W :=
  ((1/2 : ℝ)) • (fderivR f u - Aℒ (fderivR f u))

/-- Minus (conjugate-linear) part of the real derivative. -/
@[simp] def DminusCLM (f : H → W) (u : H) : H →L[ℝ] W :=
  ((1/2 : ℝ)) • (fderivR f u + Aℒ (fderivR f u))

/-- Split identity: `Df = Dplus + Dminus`. -/
@[simp] lemma Dplus_add_Dminus (f : H → W) (u : H) :
    DplusCLM (H:=H) (W:=W) f u + DminusCLM f u = fderivR f u := by
  ext v
  simp [DplusCLM, DminusCLM, Aℒ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        smul_add, add_smul, smul_neg]
  norm_num

/-! ## Complex-/conjugate-linearity in the direction (via `Jc`) -/

/-- `Dplus` commutes with `Jc`: complex-linear in the direction. -/
@[simp] lemma isCLinearR_Dplus (f : H → W) (u : H) :
    (Jc_W).comp (DplusCLM f u) = (DplusCLM f u).comp (Jc_H) := by
  ext v; simp [DplusCLM, Aℒ, sub_eq_add_neg, smul_add, add_comm, add_left_comm, add_assoc]

/-- `Dminus` anti-commutes with `Jc`: conjugate-linear in the direction. -/
@[simp] lemma isALinearR_Dminus (f : H → W) (u : H) :
    (Jc_W).comp (DminusCLM f u) = - (DminusCLM f u).comp (Jc_H) := by
  ext v; simp [DminusCLM, Aℒ, sub_eq_add_neg, smul_add, add_comm, add_left_comm, add_assoc]

/-- Pointwise decomposed form of the real Gâteaux derivative. -/
@[simp] lemma fderivR_apply_split (f : H → W) (u v : H) :
    fderivR f u v = DplusCLM f u v + DminusCLM f u v := by
  simpa using
    congrArg (fun (T : H →L[ℝ] W) => T v) (Dplus_add_Dminus (H:=H) (W:=W) f u)

end Wirtinger
