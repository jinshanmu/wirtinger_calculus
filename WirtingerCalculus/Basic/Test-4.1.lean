import mathlib

/-!
# Wirtinger Calculus

Formalizes core concepts of Wirtinger calculus for functions between complex
Hilbert spaces.

## Main Definitions:
1.  **Real Fréchet Derivative**: Derivatives with respect to `ℝ`.
2.  **Complex Structures**: The multiplication-by-`i` operator `J` and conjugations `C`.
3.  **Wirtinger Operators**: `D₊` (ℂ-linear) and `D₋` (ℂ-antilinear) parts of the derivative.
4.  **Wirtinger Gradients**: `∇₊` and `∇₋` for scalar functions via Riesz representation.
5.  **Adjoint Operators**: `ℂ`-linear and `ℂ`-antilinear adjoints.
-/

noncomputable section
open Complex
open ComplexConjugate

namespace Wirtinger

/-! ## Scalar Multiplication Helpers -/
section smul_helpers
variable {V : Type _} [AddCommGroup V] [Module ℂ V]

@[simp] lemma ofReal_smul' (r : ℝ) (v : V) :
    (r : ℂ) • v = (r : ℝ) • v := rfl

@[simp] lemma ofReal_mul_I_smul (r : ℝ) (v : V) :
    ((r : ℂ) * I) • v = r • (I • v) := by
  calc
    ((r : ℂ) * I) • v = (r : ℂ) • (I • v) := by rw [smul_smul]
    _ = (r : ℝ) • (I • v) := rfl

/-- Decomposes a `ℂ`-scalar multiplication into its real and imaginary parts. -/
lemma complexSmul_decompose (a : ℂ) (v : V) :
    a • v = (a.re : ℝ) • v + a.im • I • v := by
  calc
    a • v
        = ((a.re : ℂ) + (a.im : ℂ) * I) • v := by simp [Complex.re_add_im a]
    _   = (a.re : ℂ) • v + ((a.im : ℂ) * I) • v := by
              rw [add_smul]
    _   = (a.re : ℝ) • v + a.im • I • v := by
              simp [ofReal_mul_I_smul]

end smul_helpers

/-! ## Real Fréchet Derivative -/
universe u v
variable {H : Type u} {W : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- Real Fréchet differentiability at a point. -/
abbrev HasRDerivAt (f : H → W) (u : H) (D : H →L[ℝ] W) : Prop := HasFDerivAt f D u

/-- The real Fréchet derivative of `f` at `u`. -/
@[simp] abbrev fderivR (f : H → W) (u : H) : H →L[ℝ] W := fderiv ℝ f u

/-- The continuous `ℝ`-linear map `t ↦ t • v`. -/
@[simp] def lineCLM (v : H) : ℝ →L[ℝ] H := (1 : ℝ →L[ℝ] ℝ).smulRight v

@[simp] lemma lineCLM_apply (v : H) (t : ℝ) : lineCLM v t = t • v := by
  simp [lineCLM]

/-- Chain rule form of the real directional derivative. -/
lemma real_directional_hasDerivAt
  {f : H → W} {u v : H} {D : H →L[ℝ] W}
  (hf : HasRDerivAt f u D) :
  HasDerivAt (fun t : ℝ => f (u + t • v)) (D v) 0 := by
  have hL : HasFDerivAt (fun t : ℝ => u + lineCLM v t) (lineCLM v) 0 :=
    (lineCLM v).hasFDerivAt.const_add u
  have hf_at : HasFDerivAt f D (u + lineCLM v 0) := by
    simpa [lineCLM_apply] using hf
  have hcomp :
      HasFDerivAt (fun t : ℝ => f (u + lineCLM v t)) (D.comp (lineCLM v)) 0 :=
    hf_at.comp 0 hL
  simpa [ContinuousLinearMap.comp_apply, lineCLM_apply, one_smul] using hcomp.hasDerivAt

/-- Gâteaux derivative as the Fréchet derivative applied to a direction. -/
lemma real_directional_deriv_eq
  {f : H → W} {u v : H} {D : H →L[ℝ] W}
  (hf : HasRDerivAt f u D) :
  deriv (fun t : ℝ => f (u + t • v)) 0 = D v := by
  simpa using (real_directional_hasDerivAt (f:=f) (u:=u) (v:=v) (D:=D) hf).deriv

/-! ## Algebraic Complex Structures -/
section algebraic_J
variable {H W : Type*}
variable [AddCommGroup H] [Module ℂ H]
variable [AddCommGroup W] [Module ℂ W]

/-- Multiplication by `i` as an `ℝ`-linear map. -/
@[simp] def J (V : Type _) [AddCommGroup V] [Module ℂ V] : V →ₗ[ℝ] V where
  toFun := fun v => (I : ℂ) • v
  map_add' := by intro v w; simp [smul_add]
  map_smul' := by intro r v; simpa using (smul_comm (r : ℝ) (I : ℂ) v).symm

@[simp] lemma J_apply {V} [AddCommGroup V] [Module ℂ V] (v : V) :
    J V v = (I : ℂ) • v := rfl

/-- The identity `J ∘ J = -id`. -/
lemma J_comp_J (V : Type _) [AddCommGroup V] [Module ℂ V] :
    (J V).comp (J V) = - LinearMap.id := by
  ext v; simp [J, smul_smul, Complex.I_mul_I]

/-- An `ℝ`-linear, involutive conjugation `C` that anticommutes with `J`. -/
structure Conjugation (V : Type _) [AddCommGroup V] [Module ℂ V] where
  C : V →ₗ[ℝ] V
  involutive : C.comp C = LinearMap.id
  antiJ : C.comp (J V) = - (J V).comp C

@[simp] lemma Conjugation.comp_self_id {V} [AddCommGroup V] [Module ℂ V]
    (C : Conjugation V) :
    C.C.comp C.C = LinearMap.id := C.involutive

@[simp] lemma Conjugation.antiJ_apply {V} [AddCommGroup V] [Module ℂ V]
    (C : Conjugation V) (v : V) :
    C.C ((I : ℂ) • v) = - (I : ℂ) • C.C v := by
  have h := congrArg (fun (L : V →ₗ[ℝ] V) => L v) C.antiJ
  simp [LinearMap.comp_apply, J] at h
  simpa [neg_smul] using h

/-- Complex conjugate from real and imaginary parts. -/
@[simp] lemma star_eq_re_sub_im (a : ℂ) :
    (starRingEnd ℂ) a = (a.re : ℂ) - (a.im : ℂ) * I := by
  change star a = (a.re : ℂ) - (a.im : ℂ) * I
  rw [Complex.re_add_im a, star_add, star_mul, star_ofReal, star_I]
  simp [mul_comm]

/-- A `Conjugation` map is `ℂ`-antilinear. -/
lemma Conjugation.conj_smul {V} [AddCommGroup V] [Module ℂ V]
    (C : Conjugation V) (a : ℂ) (v : V) :
    C.C (a • v) = (star a) • C.C v := by
  have h0 : a • v = (a.re : ℝ) • v + a.im • (I • v) :=
    complexSmul_decompose (V:=V) a v
  have h_smul₁ : C.C ((a.re : ℝ) • v) = (a.re : ℝ) • C.C v :=
    C.C.map_smul (a.re : ℝ) v
  have h_smul₂ : C.C (a.im • (I • v)) = a.im • C.C (I • v) :=
    C.C.map_smul (a.im : ℝ) (I • v)
  calc
    C.C (a • v)
        = C.C ((a.re : ℝ) • v + a.im • (I • v)) := by rw [h0]
    _   = C.C ((a.re : ℝ) • v) + C.C (a.im • (I • v)) := by
            exact C.C.map_add ((a.re : ℝ) • v) (a.im • (I • v))
    _   = (a.re : ℝ) • C.C v + a.im • C.C (I • v) := by
            simp [h_smul₁, h_smul₂]
    _   = (a.re : ℝ) • C.C v + a.im • (-(I • C.C v)) := by
            simp [Conjugation.antiJ_apply]
    _   = (a.re : ℝ) • C.C v - a.im • (I • C.C v) := by
            simp [smul_neg, sub_eq_add_neg]
    _   = ((a.re : ℂ) • C.C v) - (((a.im : ℂ) * I) • C.C v) := by
            simp
    _   = ((a.re : ℂ) - (a.im : ℂ) * I) • C.C v := by
            rw [sub_smul]
    _   = (star a) • C.C v := by
            rw [star_eq_re_sub_im]

end algebraic_J

/-! ## Wirtinger Operators -/
section wirtinger_ops

/-- Multiplication by `i` as a continuous `ℝ`-linear map. -/
def Jc (V : Type _) [NormedAddCommGroup V] [NormedSpace ℂ V] : V →L[ℝ] V :=
  { toLinearMap := J V, cont := continuous_const_smul (I : ℂ) }

@[simp] lemma Jc_apply {V} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) :
    Jc V v = (I : ℂ) • v := rfl

/-- Operator-level identity `Jc ∘ Jc = -id`. -/
@[simp] lemma Jc_comp_Jc (V : Type _) [NormedAddCommGroup V] [NormedSpace ℂ V] :
    (Jc V).comp (Jc V) = - (ContinuousLinearMap.id ℝ V) := by
  ext v; simp [ContinuousLinearMap.comp_apply, Jc_apply, smul_smul, Complex.I_mul_I]

@[simp] lemma Jc_comp_Jc_apply (V : Type _) [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) :
    ((Jc V).comp (Jc V)) v = - v := by
  simp [Jc_comp_Jc V]

abbrev Jc_H : H →L[ℝ] H := Jc H
abbrev Jc_W : W →L[ℝ] W := Jc W

/-- The anti-twist operator `Aℒ(T) = Jc_W ∘ T ∘ Jc_H`. -/
@[simp] def Aℒ (T : H →L[ℝ] W) : H →L[ℝ] W := (Jc_W).comp (T.comp Jc_H)

@[simp] lemma Aℒ_apply (T : H →L[ℝ] W) (v : H) :
    Aℒ (H:=H) (W:=W) T v = (I : ℂ) • T ((I : ℂ) • v) := by
  simp [Aℒ, ContinuousLinearMap.comp_apply, Jc_apply]

/-- `Aℒ` is an involution. -/
lemma Aℒ_involutive (T : H →L[ℝ] W) :
    Aℒ (H:=H) (W:=W) (Aℒ T) = T := by
  ext v; simp [Aℒ, ContinuousLinearMap.comp_apply, Jc_apply, smul_smul, Complex.I_mul_I]

/-- Simp lemma for `Aℒ` involutivity. -/
@[simp] lemma Aℒ_Aℒ (T : H →L[ℝ] W) :
  Aℒ (H:=H) (W:=W) (Aℒ T) = T := Aℒ_involutive (H:=H) (W:=W) T

/-- The `ℂ`-linear Wirtinger operator `D₊`. -/
def DplusCLM (f : H → W) (u : H) : H →L[ℝ] W :=
  ((1/2 : ℝ)) • (fderivR f u - Aℒ (H:=H) (W:=W) (fderivR f u))

/-- The `ℂ`-antilinear Wirtinger operator `D₋`. -/
def DminusCLM (f : H → W) (u : H) : H →L[ℝ] W :=
  ((1/2 : ℝ)) • (fderivR f u + Aℒ (H:=H) (W:=W) (fderivR f u))

/-- Wirtinger split: `D₊ + D₋ = Df`. -/
lemma Dplus_add_Dminus (f : H → W) (u : H) :
    DplusCLM (H:=H) (W:=W) f u + DminusCLM f u = fderivR f u := by
  ext v
  simp only [DplusCLM, DminusCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  rw [← smul_add, sub_add_add_cancel, ← two_smul ℝ]; rw [smul_smul]; norm_num

/-- Property: `D₊` commutes with `J` (`ℂ`-linearity). -/
lemma isCLinearR_Dplus (f : H → W) (u : H) :
    (Jc_W).comp (DplusCLM f u) = (DplusCLM f u).comp (Jc_H) := by
  let D := fderivR f u
  simp_rw [DplusCLM, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
           ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  apply congr_arg ((1/2 : ℝ) • ·)
  have h1 : Jc_W.comp (Aℒ D) = -D.comp Jc_H := by
    ext x; change Jc_W (Aℒ D x) = -(D (Jc_H x))
    rw [Aℒ_apply, Jc_apply, Jc_apply, smul_smul, Complex.I_mul_I, neg_one_smul]
  have h2 : (Aℒ D).comp Jc_H = -Jc_W.comp D := by
    ext x; change Aℒ D (Jc_H x) = - (Jc_W (D x))
    rw [Aℒ_apply, Jc_apply, Jc_apply, smul_smul, Complex.I_mul_I, neg_one_smul, D.map_neg, smul_neg]
  rw [h1, h2, sub_neg_eq_add, sub_neg_eq_add, add_comm]

/-- Property: `D₋` anticommutes with `J` (`ℂ`-antilinearity). -/
lemma isALinearR_Dminus (f : H → W) (u : H) :
    (Jc_W).comp (DminusCLM f u) = - (DminusCLM f u).comp (Jc_H) := by
  let D := fderivR f u
  simp_rw [DminusCLM]
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, ← smul_neg]
  apply congr_arg ((1/2 : ℝ) • ·)
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, neg_add_rev]
  have h1 : Jc_W.comp (Aℒ D) = -D.comp Jc_H := by
    ext x; change Jc_W (Aℒ D x) = -(D (Jc_H x))
    rw [Aℒ_apply, Jc_apply, Jc_apply, smul_smul, Complex.I_mul_I, neg_one_smul]
  have h2 : (Aℒ D).comp Jc_H = -Jc_W.comp D := by
    ext x; change Aℒ D (Jc_H x) = - (Jc_W (D x))
    rw [Aℒ_apply, Jc_apply, Jc_apply, smul_smul, Complex.I_mul_I, neg_one_smul, D.map_neg, smul_neg]
  rw [h1, h2]; abel

/-- Pointwise Wirtinger split of the derivative. -/
lemma fderivR_apply_split (f : H → W) (u v : H) :
    fderivR f u v = DplusCLM f u v + DminusCLM f u v := by
  have h := congrArg (fun (T : H →L[ℝ] W) => T v) (Dplus_add_Dminus (H:=H) (W:=W) f u)
  exact h.symm
end wirtinger_ops

/-! ## Scalar-Valued Functions: `ℂ`-Linear Maps -/
section scalar_linear

/-- The `D₊` operator as a continuous `ℂ`-linear map for scalar functions. -/
def DplusCLM_c_linear (f : H → ℂ) (u : H) : H →L[ℂ] ℂ :=
{ toLinearMap :=
  { toFun := fun v => DplusCLM (H:=H) (W:=ℂ) f u v
  , map_add' := by intro x y; simp
  , map_smul' := by
      intro a v
      set D := DplusCLM (H := H) (W := ℂ) f u
      have hI : D (I • v) = I • D v := by
        have h0 := congrArg (fun (T : H →L[ℝ] ℂ) => T v)
                    (isCLinearR_Dplus (H:=H) (W:=ℂ) f u)
        simp [ContinuousLinearMap.comp_apply, Jc_apply] at h0
        exact h0.symm
      rw [complexSmul_decompose a v, D.map_add, D.map_smul, D.map_smul, hI]
      rw [← ofReal_smul', ← ofReal_smul', add_smul]
      rw [smul_smul (a.im), ← smul_assoc]
      simp [re_add_im]
      }
  , cont := (DplusCLM (H:=H) (W:=ℂ) f u).continuous }

@[simp] lemma DplusCLM_c_linear_apply (f : H → ℂ) (u v : H) :
    (DplusCLM_c_linear (H:=H) f u) v = DplusCLM (H:=H) (W:=ℂ) f u v := rfl

/-- The map `v ↦ star (D₋ v)` is `ℂ`-linear (key for `∇₋`). -/
def DminusCLM_star_c_linear (f : H → ℂ) (u : H) : H →L[ℂ] ℂ :=
{ toLinearMap :=
  { toFun := fun v => star (DminusCLM (H:=H) (W:=ℂ) f u v)
  , map_add' := by intro x y; simp [star_add]
  , map_smul' := by
      intro a v
      set D := DminusCLM (H := H) (W := ℂ) f u
      have hI_D : D (I • v) = - I • D v := by
        have h0 := congrArg (fun (T : H →L[ℝ] ℂ) => T v)
                    (isALinearR_Dminus (H:=H) (W:=ℂ) f u)
        simpa [neg_neg, ContinuousLinearMap.comp_apply] using (congrArg Neg.neg h0).symm
      rw [complexSmul_decompose a v, D.map_add, D.map_smul, D.map_smul, hI_D]
      rw [star_add, star_smul, star_smul, star_ofReal, star_ofReal, star_neg, star_smul, star_I]
      simp only [smul_neg, smul_eq_mul]
      calc a • star (D v)
        = (a.re + a.im * I) • star (D v) := by rw [re_add_im]
        _ = a.re • star (D v) + (a.im * I) • star (D v) := by rw [add_smul]
        _ = star (a.re • D v) + I * (a.im • star (D v)) := by simp [star_smul, smul_mul_assoc]
        _ = star (a.re • D v) + a.im * (I * star (D v)) := by rw [smul_eq_mul, mul_assoc]
        _ = star (a.re • D v) + a.im • star (-I * D v) := by simp [star_mul, star_neg, star_I]
        _ = star (a.re • D v) + star (a.im • (-I • D v)) := by simp [star_smul]
        _ = star (a.re • D v + a.im • (-I • D v)) := by rw [star_add]
       }
  , cont := (continuous_star.comp (DminusCLM (H:=H) (W:=ℂ) f u).continuous) }

@[simp] lemma DminusCLM_star_c_linear_apply (f : H → ℂ) (u v : H) :
    (DminusCLM_star_c_linear (H:=H) f u) v
      = star (DminusCLM (H:=H) (W:=ℂ) f u v) := rfl

end scalar_linear

/-! ## Scalar-Valued Functions: Wirtinger Gradients -/
section scalar_grad
variable [CompleteSpace H]

/-- The `∇₊` gradient, via Riesz representation of `D₊`. -/
def gradPlus (f : H → ℂ) (u : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (DplusCLM_c_linear f u)

/-- Riesz property: `inner (gradPlus f u) v = DplusCLM f u v`. -/
@[simp] lemma inner_gradPlus_eq_Dplus (f : H → ℂ) (u v : H) :
    inner (𝕜 := ℂ) (gradPlus f u) v
      = DplusCLM (H:=H) (W:=ℂ) f u v := by
  change ((InnerProductSpace.toDual ℂ H) (gradPlus f u)) v
          = DplusCLM (H:=H) (W:=ℂ) f u v
  simp [gradPlus]

/-- The `∇₋` gradient, via Riesz representation of `v ↦ star (D₋ v)`. -/
def gradMinus (f : H → ℂ) (u : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (DminusCLM_star_c_linear f u)

/-- Riesz property: `DminusCLM f u v = inner v (gradMinus f u)`. -/
@[simp] lemma Dminus_eq_inner_gradMinus (f : H → ℂ) (u v : H) :
    DminusCLM (H:=H) (W:=ℂ) f u v
      = inner (𝕜 := ℂ) v (gradMinus f u) := by
  have h : inner (𝕜 := ℂ) (gradMinus f u) v
            = star (DminusCLM (H:=H) (W:=ℂ) f u v) := by
    change ((InnerProductSpace.toDual ℂ H) (gradMinus f u)) v
            = star (DminusCLM (H:=H) (W:=ℂ) f u v)
    simp [gradMinus]
  calc
    DminusCLM (H:=H) (W:=ℂ) f u v
        = star (star (DminusCLM (H:=H) (W:=ℂ) f u v)) := by rw [star_star]
    _   = star (inner (𝕜 := ℂ) (gradMinus f u) v) := by rw [h]
    _   = inner (𝕜 := ℂ) v (gradMinus f u) := by rw [inner_conj_symm]

/-- Wirtinger split for scalar functions using gradients. -/
lemma fderivR_apply_split_grad (f : H → ℂ) (u v : H) :
    fderivR (H:=H) (W:=ℂ) f u v
      = inner (𝕜 := ℂ) (gradPlus f u) v
        + inner (𝕜 := ℂ) v (gradMinus f u) := by
  simp [inner_gradPlus_eq_Dplus, Dminus_eq_inner_gradMinus,
    fderivR_apply_split (H:=H) (W:=ℂ) f u v]

end scalar_grad

/-! ## Adjoint Operators -/
section adjoints
variable [CompleteSpace H] [CompleteSpace W]

/-- Standard Hermitian adjoint identity. -/
@[simp] lemma inner_adjoint_linear (A : H →L[ℂ] W) (x : W) (y : H) :
    inner (𝕜 := ℂ) x (A y) = inner (𝕜 := ℂ) ((ContinuousLinearMap.adjoint A) x) y := by
  rw [ContinuousLinearMap.adjoint_inner_left]

end adjoints

/- Group definitions for the conjugate-linear adjoint. -/
section ConjAdj
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Private helper functional for the antilinear adjoint. -/
private def phi (B : E → F)
    (h_add : ∀ y z, B (y + z) = B y + B z)
    (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
    (h_cont : Continuous B) (x : F) : E →L[ℂ] ℂ := by
  classical
  let L : E →ₗ[ℂ] ℂ :=
  { toFun := fun y => inner (𝕜 := ℂ) (B y) x
  , map_add' := by intro y z; rw [h_add, inner_add_left]
  , map_smul' := by
      intro a y
      rw [h_smul, inner_smul_left, smul_eq_mul, star_star a, mul_comm]
      simp
       }
  have hx : Continuous fun w : F => ((InnerProductSpace.toDual ℂ F) x) w :=
    ((InnerProductSpace.toDual ℂ F) x).continuous
  have hcomp : Continuous fun y : E =>
      ((InnerProductSpace.toDual ℂ F) x) (B y) := hx.comp h_cont
  have hstar : Continuous fun y : E => star (inner (𝕜 := ℂ) x (B y)) :=
    continuous_star.comp hcomp
  have hLcont : Continuous fun y : E => L y := by
    convert hstar using 1
    ext y; simp [L, inner_conj_symm]
  exact { toLinearMap := L, cont := hLcont }

/-- The `ℂ`-antilinear adjoint `B†`. -/
def conjAdjoint (B : E → F)
    (h_add : ∀ y z, B (y + z) = B y + B z)
    (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
    (h_cont : Continuous B) : F → E :=
  fun x => (InnerProductSpace.toDual ℂ E).symm (phi B h_add h_smul h_cont x)

/-- Unstarred inner product identity for the antilinear adjoint. -/
lemma inner_conjAdjoint (B : E → F)
    (h_add : ∀ y z, B (y + z) = B y + B z)
    (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
    (h_cont : Continuous B) (x : F) (y : E) :
    inner (𝕜 := ℂ) ((conjAdjoint B h_add h_smul h_cont) x) y = inner (𝕜 := ℂ) (B y) x := by
  classical
  change (InnerProductSpace.toDual ℂ E) ((conjAdjoint B h_add h_smul h_cont) x) y
          = inner (𝕜 := ℂ) (B y) x
  simp [conjAdjoint, phi]

/-- Defining property of the antilinear adjoint: `⟪x, B y⟫ = star ⟪B† x, y⟫`. -/
lemma inner_eq_star_adjoint (B : E → F)
    (h_add : ∀ y z, B (y + z) = B y + B z)
    (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
    (h_cont : Continuous B) (x : F) (y : E) :
    inner (𝕜 := ℂ) x (B y) =
    star (inner (𝕜 := ℂ) ((conjAdjoint B h_add h_smul h_cont) x) y) := by
  calc
    inner (𝕜 := ℂ) x (B y) = star (inner (𝕜 := ℂ) (B y) x) := by rw [inner_conj_symm]
    _ = star (inner (𝕜 := ℂ) ((conjAdjoint B h_add h_smul h_cont) x) y) := by
        rw [inner_conjAdjoint]

end ConjAdj

/-! ## Properties of Conjugations -/
section conj_push
variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- An antiunitary conjugation preserves the inner product up to `star`. -/
def Conjugation.IsAntiunitary (C : Conjugation V) : Prop :=
  ∀ x y : V, inner (𝕜 := ℂ) (C.C x) (C.C y) = star (inner (𝕜 := ℂ) x y)

@[simp] lemma Conjugation.inner_conj_conj
    (C : Conjugation V) (hC : C.IsAntiunitary) (x y : V) :
    inner (𝕜 := ℂ) (C.C x) (C.C y) = star (inner (𝕜 := ℂ) x y) := hC x y

@[simp] lemma Conjugation.inner_conj_conj_swap
    (C : Conjugation V) (hC : C.IsAntiunitary) (x y : V) :
    inner (𝕜 := ℂ) (C.C x) (C.C y) = inner (𝕜 := ℂ) y x := by
  simp [hC]

end conj_push

section conj_isometry
variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- An isometric conjugation preserves the norm. -/
def Conjugation.IsIsometry (C : Conjugation V) : Prop :=
  ∀ v, ‖C.C v‖ = ‖v‖

/-- An isometry is antiunitary (via polarization identity). -/
lemma Conjugation.isometry_to_antiunitary
    (C : Conjugation V) (hI : C.IsIsometry) :
    C.IsAntiunitary := by
  intro x y
  have polC := inner_eq_sum_norm_sq_div_four (𝕜:=ℂ) (C.C x) (C.C y)
  have A1 : ‖C.C x + C.C y‖ = ‖x + y‖ := by
    rw [← hI (x + y), C.C.map_add]
  have A2 : ‖C.C x - C.C y‖ = ‖x - y‖ := by
    rw [← hI (x - y), C.C.map_sub]
  have hxIy  : C.C (x - I • y) = C.C x + I • C.C y := by
    simp [map_sub, Conjugation.conj_smul, sub_neg_eq_add]
  have hxmyI : C.C (x + I • y) = C.C x - I • C.C y := by
    simp [map_add, Conjugation.conj_smul, sub_eq_add_neg]
  have A3 : ‖C.C x + I • C.C y‖ = ‖x - I • y‖ := by
    rw [← hxIy, hI]
  have A4 : ‖C.C x - I • C.C y‖ = ‖x + I • y‖ := by
    rw [← hxmyI, hI]
  rw [polC, inner_eq_sum_norm_sq_div_four (𝕜:=ℂ) x y]
  simp [A1, A2, A3, A4]
  ext; simp [Complex.normSq]; ring
  ext; simp [Complex.normSq]; ring

end conj_isometry

/-! ## Summary of Pointwise Identities -/

abbrev J_H : H →L[ℝ] H := Jc H
abbrev J_W : W →L[ℝ] W := Jc W

/-- Gâteaux derivative as action of `fderivR`. -/
@[simp] lemma gateaux_at_zero_eq (f : H → W) (u v : H) (D : H →L[ℝ] W)
    (hf : HasRDerivAt f u D) :
    deriv (fun t : ℝ => f (u + t • v)) 0 = D v :=
  real_directional_deriv_eq (f:=f) (u:=u) (v:=v) (D:=D) hf

/-- Pointwise `ℂ`-linearity of `D₊`. -/
@[simp] lemma Dplus_comm_J_point (f : H → W) (u v : H) :
    (DplusCLM (H:=H) (W:=W) f u) (J_H v)
      = (J_W) ((DplusCLM (H:=H) (W:=W) f u) v) := by
  have h := congrArg (fun (T : H →L[ℝ] W) => T v)
              (isCLinearR_Dplus (H:=H) (W:=W) f u)
  simpa [ContinuousLinearMap.comp_apply] using h.symm

/-- Pointwise `ℂ`-antilinearity of `D₋`. -/
@[simp] lemma Dminus_anticomm_J_point (f : H → W) (u v : H) :
    (DminusCLM (H:=H) (W:=W) f u) (J_H v)
      = - (J_W) ((DminusCLM (H:=H) (W:=W) f u) v) := by
  have h := congrArg (fun (T : H →L[ℝ] W) => T v)
              (isALinearR_Dminus (H:=H) (W:=W) f u)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h
  rw [ContinuousLinearMap.neg_apply] at h
  exact h

/-- Pointwise Wirtinger split. -/
@[simp] lemma R_split_point (f : H → W) (u v : H) :
    fderivR (H:=H) (W:=W) f u v
      = DplusCLM (H:=H) (W:=W) f u v + DminusCLM (H:=H) (W:=W) f u v :=
  fderivR_apply_split (H:=H) (W:=W) f u v

/-- Riesz identity for `D₊`. -/
@[simp] lemma riesz_plus_point [CompleteSpace H] (f : H → ℂ) (u v : H) :
    DplusCLM (H:=H) (W:=ℂ) f u v
      = inner (𝕜 := ℂ) (gradPlus f u) v :=
  (inner_gradPlus_eq_Dplus (f:=f) (u:=u) (v:=v)).symm

/-- Riesz identity for `D₋`. -/
@[simp] lemma riesz_minus_point [CompleteSpace H] (f : H → ℂ) (u v : H) :
    DminusCLM (H:=H) (W:=ℂ) f u v
      = inner (𝕜 := ℂ) v (gradMinus f u) :=
  Dminus_eq_inner_gradMinus (f:=f) (u:=u) (v:=v)

/-- Wirtinger split for scalar functions using gradients. -/
@[simp] lemma R_split_scalar_point [CompleteSpace H] (f : H → ℂ) (u v : H) :
    fderivR (H:=H) (W:=ℂ) f u v
      = inner (𝕜 := ℂ) (gradPlus f u) v
        + inner (𝕜 := ℂ) v (gradMinus f u) :=
  fderivR_apply_split_grad (f:=f) (u:=u) (v:=v)

/-- Standard Hermitian adjoint identity. -/
@[simp] lemma adjoint_linear_eq
  [CompleteSpace H] [CompleteSpace W]
  (A : H →L[ℂ] W) (x : W) (y : H) :
  inner (𝕜 := ℂ) x (A y) = inner (𝕜 := ℂ) ((ContinuousLinearMap.adjoint A) x) y := by simp

/-- Antilinear adjoint identity. -/
@[simp] lemma adjoint_antilinear_star
  [CompleteSpace H] [CompleteSpace W]
  (B : H → W)
  (h_add : ∀ y z, B (y + z) = B y + B z)
  (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
  (h_cont : Continuous B) (x : W) (y : H) :
  inner (𝕜 := ℂ) x (B y)
    = star (inner (𝕜 := ℂ) ((conjAdjoint B h_add h_smul h_cont) x) y) :=
  inner_eq_star_adjoint (B:=B) h_add h_smul h_cont x y

/-- How an isometric conjugation interacts with the inner product. -/
lemma conjugation_push_identity
    (C : Conjugation H) (hI : Conjugation.IsIsometry (V := H) C) (x y : H) :
    inner (𝕜 := ℂ) (C.C x) (C.C y)
      = star (inner (𝕜 := ℂ) x y)
      ∧ inner (𝕜 := ℂ) (C.C x) (C.C y)
      = inner (𝕜 := ℂ) y x := by
  have hA := Conjugation.isometry_to_antiunitary (V := H) C hI
  exact ⟨Conjugation.inner_conj_conj (C:=C) hA x y,
         Conjugation.inner_conj_conj_swap (C:=C) hA x y⟩

/-! ### Rules of Operation for Wirtinger Gradients -/
section rules_of_operation
open Complex
variable {H : Type _} {V : Type _} {W : Type _}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable [CompleteSpace H] [CompleteSpace V] [CompleteSpace W]

/-! ### Conjugation on `ℂ` and its interaction with `J` -/

/-- Real-linear, continuous complex conjugation on `ℂ`. -/
def Cc : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := fun z => star z
  , map_add' := by intro x y; simp
  , map_smul' := by intro r z; simp [star_smul] }
, cont := continuous_star }

@[simp] lemma Cc_apply (z : ℂ) : Cc z = star z := rfl

-- mathlib has `Complex.conj_I`, but we work with `star`.
@[simp] lemma star_I' : star (I : ℂ) = -I := by simp

/-- `J_ℂ ∘ C = - C ∘ J_ℂ`. -/
@[simp] lemma Jc_comp_Cc_anticomm :
  (Jc ℂ).comp Cc = - Cc.comp (Jc ℂ) := by
  ext z
  simp [Jc_apply, Cc_apply, smul_eq_mul, mul_comm]

/-! A small helper: composition with a fixed `ℝ`-CLM on the codomain. -/

/-- `fderivℝ` commutes with post-composition by a fixed `ℝ`-continuous linear map. -/
lemma fderivR_post {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (L : W →L[ℝ] V) (f : H → W) (u : H)
  (hf : DifferentiableAt ℝ f u) :
  fderivR (fun x => L (f x)) u = L.comp (fderivR f u) := by
  have hL : DifferentiableAt ℝ L (f u) := L.differentiableAt
  rw [fderiv_comp u hL.hasFDerivAt hf.hasFDerivAt, fderiv_continuousLinearMap]

/-! ### Conjugation rules (LaTeX (1)–(3)) -/

section conj_rules
variable (f : H → ℂ) (u : H) (hf : DifferentiableAt ℝ f u)

/-- `D₊(conj f) = C ∘ D₋(f)` (operator form). -/
lemma Dplus_conj_op :
  DplusCLM (fun x => star (f x)) u = (Cc).comp (DminusCLM f u) := by
  let Df := fderivR f u
  have hf_star_diff : DifferentiableAt ℝ (fun x => star (f x)) u :=
    differentiableAt_star.comp u hf
  have hDf_conj : fderivR (fun x => star (f x)) u = Cc.comp Df :=
    fderivR_post Cc f u hf
  have hA : Aℒ (fderivR (fun x => star (f x)) u) = -Cc.comp (Aℒ Df) := by
    rw [hDf_conj, Aℒ, ContinuousLinearMap.comp_assoc, Jc_comp_Cc_anticomm]
    simp [ContinuousLinearMap.comp_assoc]
  unfold DplusCLM DminusCLM
  rw [hDf_conj, hA, smul_sub, smul_neg, sub_neg_eq_add]
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_add]
  congr
  rw [ContinuousLinearMap.comp_smul]

/-- `D₋(conj f) = C ∘ D₊(f)` (operator form). -/
lemma Dminus_conj_op :
  DminusCLM (fun x => star (f x)) u = (Cc).comp (DplusCLM f u) := by
  let Df := fderivR f u
  have hf_star_diff : DifferentiableAt ℝ (fun x => star (f x)) u :=
    differentiableAt_star.comp u hf
  have hDf_conj : fderivR (fun x => star (f x)) u = Cc.comp Df :=
    fderivR_post Cc f u hf
  have hA : Aℒ (fderivR (fun x => star (f x)) u) = -Cc.comp (Aℒ Df) := by
    rw [hDf_conj, Aℒ, ContinuousLinearMap.comp_assoc, Jc_comp_Cc_anticomm]
    simp [ContinuousLinearMap.comp_assoc]
  unfold DplusCLM DminusCLM
  rw [hDf_conj, hA, smul_add]
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_sub]
  congr

/-- `∇₊(conj f) = ∇₋ f` and `∇₋(conj f) = ∇₊ f`. -/
lemma grad_conj_swap :
  gradPlus (fun x => star (f x)) u = gradMinus f u
  ∧ gradMinus (fun x => star (f x)) u = gradPlus f u := by
  constructor
  · ext v
    rw [inner_gradPlus_eq_Dplus, Dplus_conj_op f u hf, ContinuousLinearMap.comp_apply, Cc_apply]
    rw [star_star, Dminus_eq_inner_gradMinus, inner_conj_symm]
  · ext v
    rw [Dminus_eq_inner_gradMinus]
    calc
      inner (𝕜 := ℂ) v (gradMinus (fun x => star (f x)) u)
        = star (star (inner (𝕜 := ℂ) v (gradMinus (fun x => star (f x)) u))) := by rw [star_star]
      _ = star (inner (𝕜 := ℂ) (gradMinus (fun x => star (f x)) u) v) := by rw [inner_conj_symm]
      _ = star (DminusCLM_star_c_linear_apply _ _ _) := rfl
      _ = star (star (DminusCLM (fun x => star (f x)) u v)) := rfl
      _ = DminusCLM (fun x => star (f x)) u v := by rw [star_star]
      _ = (Cc.comp (DplusCLM f u)) v := by rw [Dminus_conj_op f u hf]
      _ = star (DplusCLM f u v) := rfl
      _ = star (inner (𝕜 := ℂ) (gradPlus f u) v) := by rw [inner_gradPlus_eq_Dplus]
      _ = inner (𝕜 := ℂ) v (gradPlus f u) := by rw [inner_conj_symm]

end conj_rules

/-! ### Algebraic operations (scalar combos & product/quotient) -/

section algebra_ops
variable (f g : H → ℂ) (u : H)
variable (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)

/-- Multiplication by a fixed scalar, viewed as an `ℝ`-CLM on `ℂ`. -/
def mulCLM (a : ℂ) : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := fun z => a * z
  , map_add' := by intro x y; simp [mul_add]
  , map_smul' := by intro r z; simp [smul_eq_mul]; ac_rfl }
, cont := by
    simpa using (continuous_const.mul continuous_id) }

lemma Aℒ_post_mul (a : ℂ) (T : H →L[ℝ] ℂ) :
  Aℒ ((mulCLM a).comp T) = (mulCLM a).comp (Aℒ T) := by
  ext v; unfold Aℒ Jc J; simp [mulCLM, ContinuousLinearMap.comp_apply, smul_eq_mul, mul_assoc, mul_comm a I]

/-- `D₊(a f) = a • D₊ f` and `D₋(a f) = a • D₋ f` (operator level). -/
lemma Dpm_smul (a : ℂ) :
  DplusCLM (fun x => a * f x) u = (mulCLM a).comp (DplusCLM f u) ∧
  DminusCLM (fun x => a * f x) u = (mulCLM a).comp (DminusCLM f u) := by
  have hf_mul : DifferentiableAt ℝ (fun x => a * f x) u := hf.const_mul a
  have hDf : fderivR (fun x => a * f x) u = (mulCLM a).comp (fderivR f u) :=
    fderivR_post (mulCLM a) f u hf
  have hA : Aℒ (fderivR (fun x => a * f x) u) = (mulCLM a).comp (Aℒ (fderivR f u)) := by
    rw [hDf, Aℒ_post_mul]
  constructor
  · unfold DplusCLM; rw [hDf, hA, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_sub]; rfl
  · unfold DminusCLM; rw [hDf, hA, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_add]; rfl

/-- Scalar combination of `∇₊`. -/
lemma gradPlus_scomb (α β : ℂ) :
  gradPlus (fun x => α * f x + β * g x) u
    = (star α) • gradPlus f u + (star β) • gradPlus g u := by
  ext v
  rw [inner_gradPlus_eq_Dplus, inner_add_left, inner_smul_left, inner_smul_left]
  have h_add_diff := (hf.const_mul α).add (hg.const_mul β)
  unfold DplusCLM
  rw [fderiv_add h_add_diff.hasFDerivAt (hf.const_mul α).hasFDerivAt (hg.const_mul β).hasFDerivAt]
  simp only [Aℒ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, map_add]
  rw [fderiv_const_mul hf.hasFDerivAt, fderiv_const_mul hg.hasFDerivAt]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  rw [Aℒ_post_mul, Aℒ_post_mul]
  simp [mulCLM, DplusCLM, inner_gradPlus_eq_Dplus, mul_sub, mul_add]
  ring

/-- Scalar combination of `∇₋`. -/
lemma gradMinus_scomb (α β : ℂ) :
  gradMinus (fun x => α * f x + β * g x) u
    = α • gradMinus f u + β • gradMinus g u := by
  ext v
  rw [Dminus_eq_inner_gradMinus, inner_add_right, inner_smul_right, inner_smul_right]
  have h_add_diff := (hf.const_mul α).add (hg.const_mul β)
  unfold DminusCLM
  rw [fderiv_add h_add_diff.hasFDerivAt (hf.const_mul α).hasFDerivAt (hg.const_mul β).hasFDerivAt]
  simp only [Aℒ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_add]
  rw [fderiv_const_mul hf.hasFDerivAt, fderiv_const_mul hg.hasFDerivAt]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply]
  rw [Aℒ_post_mul, Aℒ_post_mul]
  simp [mulCLM, DminusCLM, Dminus_eq_inner_gradMinus, mul_add]
  ac_rfl


/-- Product rule for Wirtinger gradients. -/
lemma grad_prod :
  gradPlus (fun x => f x * g x) u
    = (star (f u)) • gradPlus g u + (star (g u)) • gradPlus f u
  ∧
  gradMinus (fun x => f x * g x) u
    = (f u) • gradMinus g u + (g u) • gradMinus f u := by
  have hprod : DifferentiableAt ℝ (fun x => f x * g x) u := hf.mul hg
  have hDf : fderivR (fun x => f x * g x) u
      = (mulCLM (f u)).comp (fderivR g u) + (mulCLM (g u)).comp (fderivR f u) :=
    fderiv_mul hf.hasFDerivAt hg.hasFDerivAt
  have hA : Aℒ (fderivR (fun x => f x * g x) u)
      = (mulCLM (f u)).comp (Aℒ (fderivR g u))
        + (mulCLM (g u)).comp (Aℒ (fderivR f u)) := by
    rw [hDf, map_add, Aℒ_post_mul, Aℒ_post_mul]
  have hDplus : DplusCLM (fun x => f x * g x) u
      = (mulCLM (f u)).comp (DplusCLM g u) + (mulCLM (g u)).comp (DplusCLM f u) := by
    unfold DplusCLM; rw [hDf, hA]; simp [mulCLM]; ext; simp [mul_sub, mul_add]; ring
  have hDminus : DminusCLM (fun x => f x * g x) u
      = (mulCLM (f u)).comp (DminusCLM g u) + (mulCLM (g u)).comp (DminusCLM f u) := by
    unfold DminusCLM; rw [hDf, hA]; simp [mulCLM]; ext; simp [mul_add]; ring
  constructor
  · ext v
    simp [inner_gradPlus_eq_Dplus, hDplus, mulCLM, ContinuousLinearMap.comp_apply,
          inner_add_left, inner_smul_left, star_star]
  · ext v
    simp [Dminus_eq_inner_gradMinus, hDminus, mulCLM, ContinuousLinearMap.comp_apply,
          inner_add_right, inner_smul_right]

/-- Reciprocal (on `g u ≠ 0`) and quotient rules. -/
lemma grad_recip_quot (hg0 : g u ≠ 0) :
  gradPlus (fun x => (g x)⁻¹) u = - ((star (g u)⁻¹)^2 • gradPlus g u)
  ∧
  gradMinus (fun x => (g x)⁻¹) u = - ((g u)⁻² • gradMinus g u)
  ∧
  gradPlus (fun x => f x / g x) u
    = (star (g u)⁻¹) • gradPlus f u - (star (f u) * star (g u)⁻¹^2) • gradPlus g u
  ∧
  gradMinus (fun x => f x / g x) u
    = (g u)⁻¹ • gradMinus f u - (f u * (g u)⁻² ) • gradMinus g u := by
  have hg_inv_diff : DifferentiableAt ℝ (fun x => (g x)⁻¹) u := hg.inv hg0
  have h_one : (fun _ : H => (1 : ℂ)) = fun x => g x * (g x)⁻¹ := by ext x; rw [mul_inv_cancel (hg0)]
  have h_grad_one := grad_prod g (fun x => (g x)⁻¹) u hg hg_inv_diff
  have h_const_grad_plus : gradPlus (fun _ : H => (1:ℂ)) u = 0 := by ext v; simp
  have h_const_grad_minus : gradMinus (fun _ : H => (1:ℂ)) u = 0 := by ext v; simp
  rw [h_one] at h_const_grad_plus h_const_grad_minus
  have h_plus_solve : (star (g u)) • gradPlus (fun x => (g x)⁻¹) u = - (star (g u)⁻¹) • gradPlus g u := by
    simpa [h_const_grad_plus] using h_grad_one.1
  have h_minus_solve : (g u) • gradMinus (fun x => (g x)⁻¹) u = - (g u)⁻¹ • gradMinus g u := by
    simpa [h_const_grad_minus] using h_grad_one.2
  have h_rec_plus : gradPlus (fun x => (g x)⁻¹) u = - ((star (g u)⁻¹)^2 • gradPlus g u) := by
    have h_inv_smul := congr_arg ((star (g u))⁻¹ • ·) h_plus_solve
    rw [smul_smul, star_inv, ← mul_smul, inv_mul_cancel (star_ne_zero.mpr hg0), one_smul] at h_inv_smul
    rw [h_inv_smul, smul_smul, ← pow_two]
  have h_rec_minus : gradMinus (fun x => (g x)⁻¹) u = - ((g u)⁻² • gradMinus g u) := by
    have h_inv_smul := congr_arg ((g u)⁻¹ • ·) h_minus_solve
    rw [smul_smul, ← mul_smul, inv_mul_cancel hg0, one_smul] at h_inv_smul
    rw [h_inv_smul, smul_smul, ← pow_two]
  have h_quot_prod := grad_prod f (fun x => (g x)⁻¹) u hf hg_inv_diff
  have h_quot_plus := by
    rw [h_quot_prod.1, h_rec_plus]
    simp [smul_add, smul_smul, add_comm, sub_eq_add_neg, mul_comm]
  have h_quot_minus := by
    rw [h_quot_prod.2, h_rec_minus]
    simp [smul_add, smul_smul, add_comm, sub_eq_add_neg, mul_comm]
  simp [*, div_eq_mul_inv]

end algebra_ops

/-! ### Real and complex gradients -/

section real_complex_grad
variable (f : H → ℂ) (u : H)

/-- If `f` is real-valued at every point, then `∇₊ f = ∇₋ f`. -/
lemma grad_real_eq (hf_diff : DifferentiableAt ℝ f u) (hreal : ∀ x, star (f x) = f x) :
  gradPlus f u = gradMinus f u := by
  have h_grad_swap := (grad_conj_swap f u hf_diff).1
  rwa [funext hreal] at h_grad_swap

/-- Real-derivative identity `Df[u][v] = 2 * Re ⟪∇ℝ f[u], v⟫` for real-valued `f`. -/
lemma real_derivative_formula (hf_diff : DifferentiableAt ℝ f u) (hreal : ∀ x, star (f x) = f x) (v : H) :
  fderivR f u v
    = 2 * Complex.re (inner (𝕜 := ℂ) (gradPlus f u) v) := by
  have hgr : gradPlus f u = gradMinus f u := grad_real_eq f u hf_diff hreal
  rw [R_split_scalar_point, hgr, inner_conj_symm]
  simp [two_mul, Complex.re]

/-- If `f` is holomorphic at `u` (i.e. `∇₋ f[u] = 0`), then `∇_ℂ f[u] = ∇₊ f[u]`. -/
def gradComplex (f : H → ℂ) (u : H) : H := gradPlus f u
@[simp] lemma gradComplex_eq_gradPlus
  (_ : gradMinus f u = 0) : gradComplex f u = gradPlus f u := by simp [gradComplex]

end real_complex_grad

/-! ### Chain rule (general form) -/

section chain_rule
variable (g : H → V) (f : V → ℂ) (u : H)
variable (hg : DifferentiableAt ℝ g u) (hf : DifferentiableAt ℝ f (g u))

/-- Upgrade `D₊ g[u]` to a `ℂ`-CLM (we only need it for the adjoint). -/
def DplusCLM_clinear' (g : H → V) (u : H) : H →L[ℂ] V :=
{ toLinearMap :=
  { toFun := fun v => DplusCLM g u v
  , map_add' := by intro x y; simp
  , map_smul' := by
      intro a v
      set D := DplusCLM g u
      have hI : D (I • v) = I • D v := by
        have h0 := congrArg (fun (T : H →L[ℝ] V) => T v) (isCLinearR_Dplus g u)
        simp [ContinuousLinearMap.comp_apply, Jc_apply] at h0
        exact h0.symm
      rw [complexSmul_decompose a v, map_add, map_smul, map_smul, hI, ← ofReal_smul', ← ofReal_smul',
        add_smul, smul_smul (a.im), ← smul_assoc]
      simp [re_add_im]
      rfl
  }
, cont := (DplusCLM g u).continuous }

/-- `D₋ g[u]` is additive and antilinear in the argument (for `conjAdjoint`). -/
lemma Dminus_add_smul :
  (∀ x y, DminusCLM g u (x + y) = DminusCLM g u x + DminusCLM g u y)
  ∧ (∀ (a : ℂ) x, DminusCLM g u (a • x) = (star a) • DminusCLM g u x) := by
  constructor
  · intro x y; simp
  · intro a x
    set D := DminusCLM g u
    have hI : D (I • x) = - I • D x := by
      have h0 := congrArg (fun (T : H →L[ℝ] V) => T x) (isALinearR_Dminus g u)
      simpa [neg_neg, ContinuousLinearMap.comp_apply, Jc_apply] using (congrArg Neg.neg h0).symm
    rw [complexSmul_decompose a x, map_add, map_smul, map_smul, hI]
    rw [← ofReal_smul', ← ofReal_smul', sub_smul, smul_neg, smul_smul, smul_smul]
    simp [star_eq_re_sub_im]
    rfl

/-- General chain rule for Wirtinger gradients. -/
lemma grad_chain_rule :
  gradPlus (fun x => f (g x)) u
    = (conjAdjoint (DminusCLM g u)
        (Dminus_add_smul g u).1 (Dminus_add_smul g u).2 (DminusCLM g u).continuous)
        (gradPlus f (g u))
    + (ContinuousLinearMap.adjoint (DplusCLM_clinear' g u))
        (gradMinus f (g u))
  ∧
  gradMinus (fun x => f (g x)) u
    = (ContinuousLinearMap.adjoint (DplusCLM_clinear' g u))
        (gradPlus f (g u))
    + (conjAdjoint (DminusCLM g u)
        (Dminus_add_smul g u).1 (Dminus_add_smul g u).2 (DminusCLM g u).continuous)
        (gradMinus f (g u)) := by
  set A := DplusCLM g u
  set B := DminusCLM g u
  set p := gradPlus f (g u)
  set q := gradMinus f (g u)
  set A_op := DplusCLM_clinear' g u
  set B_op := conjAdjoint B (Dminus_add_smul g u).1 (Dminus_add_smul g u).2 B.continuous
  have h_fcomp_diff : DifferentiableAt ℝ (f ∘ g) u := hf.comp u hg
  have h_fderiv_comp : fderivR (f ∘ g) u = (fderivR f (g u)).comp (fderivR g u) :=
    fderiv_comp u hf.hasFDerivAt hg.hasFDerivAt
  have h_split_fderiv_comp : ∀ v, fderivR (f ∘ g) u v =
      inner p (A v) + inner p (B v) + inner (A v) q + inner (B v) q := by
    intro v
    rw [h_fderiv_comp, ContinuousLinearMap.comp_apply, Dplus_add_Dminus g u]
    simp only [ContinuousLinearMap.add_apply, map_add]
    rw [R_split_scalar_point, R_split_scalar_point]
    ring
  have Dplus_fg_v : ∀ v, DplusCLM (f ∘ g) u v = inner (𝕜 := ℂ) p (B v) + inner (𝕜 := ℂ) (A v) q := by
    intro v; simp [DplusCLM, h_split_fderiv_comp, Aℒ, Jc_apply, smul_eq_mul]
    have h_Bv : inner (𝕜 := ℂ) p (I • B v) = -I * inner (𝕜 := ℂ) p (B v) := by rw [inner_smul_right, star_I]
    have h_Av : inner (𝕜 := ℂ) (I • A v) q = I * inner (𝕜 := ℂ) (A v) q := inner_smul_left
    simp [isCLinearR_Dplus g u, isALinearR_Dminus g u, ContinuousLinearMap.comp_apply, Jc_apply, h_Bv, h_Av]
    ring
  have Dminus_fg_v : ∀ v, DminusCLM (f ∘ g) u v = inner (𝕜 := ℂ) p (A v) + inner (𝕜 := ℂ) (B v) q := by
    intro v; simp [DminusCLM, h_split_fderiv_comp, Aℒ, Jc_apply, smul_eq_mul]
    have h_Bv : inner (𝕜 := ℂ) p (I • B v) = -I * inner (𝕜 := ℂ) p (B v) := by rw [inner_smul_right, star_I]
    have h_Av : inner (𝕜 := ℂ) (I • A v) q = I * inner (𝕜 := ℂ) (A v) q := inner_smul_left
    simp [isCLinearR_Dplus g u, isALinearR_Dminus g u, ContinuousLinearMap.comp_apply, Jc_apply, h_Bv, h_Av]
    ring
  constructor
  · ext v
    rw [inner_gradPlus_eq_Dplus, Dplus_fg_v, inner_add_left]
    rw [inner_eq_star_adjoint, star_star, inner_conjAdjoint]
    rw [inner_adjoint_linear]
  · ext v
    rw [Dminus_eq_inner_gradMinus, Dminus_fg_v, inner_add_right]
    rw [inner_conj_symm, inner_eq_star_adjoint, star_star, inner_conjAdjoint, inner_conj_symm]
    rw [inner_adjoint_linear]

end chain_rule

/-! ### Useful specializations of the chain rule -/

section chain_special

/-- Inner affine map `g u = A u + b` with `A` ℂ-linear: `∇₊(f∘g) = A† ∇₊ f∘g`, etc. -/
lemma grad_chain_inner_affine
  (A : H →L[ℂ] H) (b : H) (f : H → ℂ) (u : H)
  (hf : DifferentiableAt ℝ f (A u + b)) :
  gradPlus (fun x => f (A x + b)) u
    = (ContinuousLinearMap.adjoint A) (gradMinus f (A u + b))
  ∧
  gradMinus (fun x => f (A x + b)) u
    = (ContinuousLinearMap.adjoint A) (gradPlus f (A u + b)) := by
  let g := fun x => A x + b
  have hg : DifferentiableAt ℝ g u := (A.differentiableAt).add (differentiableAt_const b)
  have hg_deriv : fderivR g u = A.restrictScalars ℝ := by
    have hA_fderiv : fderiv ℝ A u = A.restrictScalars ℝ := A.hasFDerivAt.fderiv
    have hb_fderiv : fderiv ℝ (fun _ => b) u = 0 := fderiv_const b
    rw [fderiv_add hg.hasFDerivAt A.differentiableAt (differentiableAt_const b), hA_fderiv, hb_fderiv, add_zero]
  have hA_comm_J : (Jc H).comp (A.restrictScalars ℝ) = (A.restrictScalars ℝ).comp (Jc H) := by
    ext v; simp [ContinuousLinearMap.comp_apply, Jc_apply, A.map_smul]
  have h_Dplus_g : DplusCLM g u = A.restrictScalars ℝ := by
    ext v; simp [DplusCLM, hg_deriv, Aℒ, hA_comm_J, Jc_comp_Jc_apply, smul_sub, sub_neg_eq_add, invOf_two_smul_add_two_smul]
  have h_Dminus_g : DminusCLM g u = 0 := by
    ext v; simp [DminusCLM, hg_deriv, Aℒ, hA_comm_J, Jc_comp_Jc_apply, smul_add, add_neg_self]
  have h_chain := grad_chain_rule g f u hg hf
  have h_adj_Dplus : ContinuousLinearMap.adjoint (DplusCLM_clinear' g u) = ContinuousLinearMap.adjoint A := by
    ext v w; simp [DplusCLM_clinear', h_Dplus_g, inner_adjoint_linear]
  have h_adj_Dminus : (conjAdjoint (DminusCLM g u) (by simp) (by simp) (by simp)) = 0 := by
    ext v w; simp [h_Dminus_g, inner_conjAdjoint]
  simp [h_chain, h_adj_Dplus, h_adj_Dminus]

/-- Outer scalar function specialization with `V = ℂ`. -/
lemma grad_chain_outer_scalar (g : H → ℂ) (f : ℂ → ℂ) (u : H)
  (hg : DifferentiableAt ℝ g u) (hf : DifferentiableAt ℝ f (g u)) :
  gradPlus (fun x => f (g x)) u
    = (gradPlus f (g u)) • gradMinus g u + (gradMinus f (g u)) • gradPlus g u
  ∧
  gradMinus (fun x => f (g x)) u
    = (gradPlus f (g u)) • gradPlus g u + (gradMinus f (g u)) • gradMinus g u := by
  set A_op := DplusCLM_clinear' g u
  set B_op_fun := DminusCLM g u
  set B_op := conjAdjoint B_op_fun (Dminus_add_smul g u).1 (Dminus_add_smul g u).2 B_op_fun.continuous
  have hA : ∀ (c : ℂ), (ContinuousLinearMap.adjoint A_op) c = (star c) • gradPlus g u := by
    intro c; ext v; simp [inner_adjoint_linear, inner_smul_left]
  have hB : ∀ (c : ℂ), B_op c = c • gradMinus g u := by
    intro c; ext v; simp [inner_conjAdjoint, inner_smul_right, Dminus_eq_inner_gradMinus]
  have h_chain := grad_chain_rule g f u hg hf
  simp [h_chain, hA (gradPlus f (g u)), hA (gradMinus f (g u)), hB (gradPlus f (g u)), hB (gradMinus f (g u)), add_comm, smul_add]
  exact ⟨by ac_rfl, by ac_rfl⟩

end chain_special

/-! ### Unitary transport (derivative & gradient levels) -/

section unitary_transport
variable {Ĥ : Type _} [NormedAddCommGroup Ĥ] [InnerProductSpace ℂ Ĥ] [CompleteSpace Ĥ]

/-- Transport of `D₊/D₋` under a unitary `U : H ≃ₗᵢ[ℂ] Ĥ`. -/
lemma Dpm_unitary (U : H ≃ₗᵢ[ℂ] Ĥ) (f : H → ℂ) (u : H)
  (hf : DifferentiableAt ℝ f u):
  DplusCLM (H:=Ĥ) (fun û => f (U.symm û)) (U u) = (DplusCLM f u).comp (U.symm.toContinuousLinearMap.restrictScalars ℝ)
  ∧
  DminusCLM (H:=Ĥ) (fun û => f (U.symm û)) (U u) = (DminusCLM f u).comp (U.symm.toContinuousLinearMap.restrictScalars ℝ) := by
  have hf_comp : DifferentiableAt ℝ (f ∘ U.symm) (U u) := hf.comp (U u) U.symm.differentiableAt
  have h_fderiv_comp : fderiv ℝ (f ∘ U.symm) (U u) = (fderiv ℝ f u).comp (U.symm.restrictScalars ℝ) :=
    fderiv_comp (U u) hf.hasFDerivAt U.symm.differentiableAt.hasFDerivAt
  have U_comm_J : (Jc Ĥ).comp (U.toContinuousLinearMap.restrictScalars ℝ) = (U.toContinuousLinearMap.restrictScalars ℝ).comp (Jc H) := by
    ext v; simp [LinearIsometry.map_smul]
  have U_symm_comm_J : (Jc H).comp U.symm.toContinuousLinearMap.restrictScalars ℝ = (U.symm.toContinuousLinearMap.restrictScalars ℝ).comp (Jc Ĥ) := by
    ext v; simp [LinearIsometryEquiv.map_smul]
  have hA : Aℒ (fderivR (f ∘ U.symm) (U u)) = (Aℒ (fderivR f u)).comp U.symm.toContinuousLinearMap.restrictScalars ℝ := by
    simp [Aℒ, h_fderiv_comp, U_symm_comm_J, U_comm_J, ContinuousLinearMap.comp_assoc]
  constructor
  · unfold DplusCLM; rw [h_fderiv_comp, hA, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_sub]; rfl
  · unfold DminusCLM; rw [h_fderiv_comp, hA, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_add]; rfl

/-- Gradient transport under a unitary `U : H ≃ₗᵢ[ℂ] Ĥ`. -/
lemma grad_unitary (U : H ≃ₗᵢ[ℂ] Ĥ) (f : H → ℂ) (u : H)
  (hf : DifferentiableAt ℝ f u):
  gradPlus (H:=Ĥ) (fun û => f (U.symm û)) (U u) = U (gradPlus f u)
  ∧
  gradMinus (H:=Ĥ) (fun û => f (U.symm û)) (U u) = U (gradMinus f u) := by
  have hD := Dpm_unitary U f u hf
  constructor
  · ext v_hat
    rw [inner_gradPlus_eq_Dplus, hD.1, ContinuousLinearMap.comp_apply, inner_gradPlus_eq_Dplus,
        LinearIsometryEquiv.inner_map_map]
  · ext v_hat
    rw [Dminus_eq_inner_gradMinus, hD.2, ContinuousLinearMap.comp_apply, Dminus_eq_inner_gradMinus,
        LinearIsometryEquiv.inner_map_map]

end unitary_transport

end rules_of_operation

end Wirtinger
