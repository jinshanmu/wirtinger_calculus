import Mathlib

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
  have h1 :
      star a = star ((a.re : ℂ) + (a.im : ℂ) * I) := by
    exact (congrArg star (Complex.re_add_im a)).symm
  have h2 :
      star ((a.re : ℂ) + (a.im : ℂ) * I)
        = (a.re : ℂ) - (a.im : ℂ) * I := by
    simp [sub_eq_add_neg, mul_comm]
  exact h1.trans h2

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
            simp [star_eq_re_sub_im, sub_eq_add_neg]

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
      have hv := complexSmul_decompose (V:=H) a v
      have hR : D (a • v) = a.re • D v + a.im • D (I • v) := by
        have := congrArg D hv; simp [D.map_add, D.map_smul] at this; exact this
      have hR_mul :
          D (a • v) = (a.re : ℂ) * D v + (a.im : ℂ) * D (I • v) := by
        simpa [Algebra.smul_def] using hR
      have hI' : D (I • v) = I * D v := by simpa [Algebra.smul_def] using hI
      have hR_mul' :
          D (a • v) = (a.re : ℂ) * D v + (a.im : ℂ) * (I * D v) := by
        simpa [hI'] using hR_mul
      have hfact :
          (a.re : ℂ) * D v + (a.im : ℂ) * (I * D v)
            = ((a.re : ℂ) + (a.im : ℂ) * I) * D v := by
        have : (a.im : ℂ) * (I * D v) = ((a.im : ℂ) * I) * D v := by
          simp [mul_assoc]
        simpa [add_mul, this] using
          (add_mul (a.re : ℂ) ((a.im : ℂ) * I) (D v)).symm
      calc
        D (a • v)
            = (a.re : ℂ) * D v + (a.im : ℂ) * (I * D v) := hR_mul'
        _   = ((a.re : ℂ) + (a.im : ℂ) * I) * D v := hfact
        _   = a * D v := by simp [Complex.re_add_im a]
        _   = a • D v := by simp }
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
      let G : H →L[ℝ] ℂ :=
      { toLinearMap :=
        { toFun := fun y => star (D y)
        , map_add' := by intro x y; simp
        , map_smul' := by intro r x; simp }
      , cont := (continuous_star.comp D.continuous) }
      have hI_D : D (I • v) = - I • D v := by
        have h0 := congrArg (fun (T : H →L[ℝ] ℂ) => T v)
                    (isALinearR_Dminus (H:=H) (W:=ℂ) f u)
        have h' := congrArg Neg.neg h0
        simpa [neg_neg] using h'.symm
      have hmul : D (I • v) = (-I) * D v := by simpa [Algebra.smul_def] using hI_D
      have h_star : star (D (I • v)) = star (D v) * I := by
        calc
          star (D (I • v)) = star ((-I) * D v) := by rw [hmul]
          _ = star (D v) * star (-I) := by rw [star_mul]
          _ = star (D v) * I := by simp
      have hI_G : I * G v = G (I • v) := by
        change I * star (D v) = star (D (I • v)); simp [h_star, mul_comm]
      have hv := complexSmul_decompose (V:=H) a v
      have hR : G (a • v) = a.re • G v + a.im • G (I • v) := by
        have := congrArg G hv; simp [G.map_add, G.map_smul] at this; exact this
      have hR_mul :
          G (a • v) = (a.re : ℂ) * G v + (a.im : ℂ) * G (I • v) := by
        simpa [Algebra.smul_def] using hR
      have hR_mul' :
          G (a • v) = (a.re : ℂ) * G v + (a.im : ℂ) * (I * G v) := by
        simpa [hI_G] using hR_mul
      have hfact :
          (a.re : ℂ) * G v + (a.im : ℂ) * (I * G v)
            = ((a.re : ℂ) + (a.im : ℂ) * I) * G v := by
        have : (a.im : ℂ) * (I * G v) = ((a.im : ℂ) * I) * G v := by
          simp [mul_assoc]
        simpa [add_mul, this] using
          (add_mul (a.re : ℂ) ((a.im : ℂ) * I) (G v)).symm
      calc
        G (a • v)
            = (a.re : ℂ) * G v + (a.im : ℂ) * (I * G v) := hR_mul'
        _   = ((a.re : ℂ) + (a.im : ℂ) * I) * G v := hfact
        _   = a * G v := by simp [Complex.re_add_im a]
        _   = a • G v := by simp }
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
        = star (star (DminusCLM (H:=H) (W:=ℂ) f u v)) := by simp
    _   = star (inner (𝕜 := ℂ) (gradMinus f u) v) := by rw [h]
    _   = inner (𝕜 := ℂ) v (gradMinus f u) := by simp

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
  exact (ContinuousLinearMap.adjoint_inner_left (A := A) (x := y) (y := x)).symm
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
  , map_smul' := by intro a y; rw [h_smul, inner_smul_left]; simp }
  have hx : Continuous fun w : F => ((InnerProductSpace.toDual ℂ F) x) w :=
    ((InnerProductSpace.toDual ℂ F) x).continuous
  have hcomp : Continuous fun y : E =>
      ((InnerProductSpace.toDual ℂ F) x) (B y) := hx.comp h_cont
  have hstar : Continuous fun y : E => star (inner (𝕜 := ℂ) x (B y)) :=
    continuous_star.comp hcomp
  have hLcont : Continuous fun y : E => L y := by
    convert hstar using 1
    ext y; simp only [L]; simp
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
    inner (𝕜 := ℂ) x (B y) = star (inner (𝕜 := ℂ) (B y) x) := by simp
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
  simpa [inner_conj_symm] using hC x y

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
  have polC' := polC
  simp [A1, A2, A4, A3] at polC'
  rw [polC']
  rw [inner_eq_sum_norm_sq_div_four (𝕜:=ℂ) x y]
  let n := (↑‖x + y‖ ^ 2 - ↑‖x - y‖ ^ 2
    + (↑‖x + I • y‖ ^ 2 - ↑‖x - I • y‖ ^ 2) * I)
  let m := (↑‖x + y‖ ^ 2 - ↑‖x - y‖ ^ 2
    + (↑‖x - I • y‖ ^ 2 - ↑‖x + I • y‖ ^ 2) * I)
  have num_eq : n = star m := by
    classical
    have hstar : star m = (↑‖x + y‖ ^ 2 - ↑‖x - y‖ ^ 2)
        + (↑‖x - I • y‖ ^ 2 - ↑‖x + I • y‖ ^ 2) * (-I) := by
      simp [m, sub_eq_add_neg]
    have hflip : (↑‖x - I • y‖ ^ 2 - ↑‖x + I • y‖ ^ 2) * (-I)
          = (↑‖x + I • y‖ ^ 2 - ↑‖x - I • y‖ ^ 2) * I := by
      ring
    have : star m = (↑‖x + y‖ ^ 2 - ↑‖x - y‖ ^ 2)
        + (↑‖x + I • y‖ ^ 2 - ↑‖x - I • y‖ ^ 2) * I := by
      simpa [hflip, add_comm, add_left_comm, add_assoc] using hstar
    simpa [n] using this.symm
  have num_eq_div : n / (4:ℂ) = (star m) / (4:ℂ) := by
    simpa [div_eq_mul_inv] using congrArg (fun z => z / (4:ℂ)) num_eq
  have hfinal : n / (4:ℂ) = star (m / (4:ℂ)) := by
    have hsd : star (m / (4:ℂ)) = (star m) / (4:ℂ) := by simp
    simpa [hsd] using num_eq_div
  change n / (4:ℂ) = star (m / (4:ℂ))
  exact hfinal

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
  have h' := congrArg Neg.neg h
  simpa [ContinuousLinearMap.comp_apply, neg_neg] using h'.symm

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

/-! ## Rules of Operation for Wirtinger Gradients -/
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
  , map_smul' := by intro r z; simp }
, cont := continuous_star }

@[simp] lemma Cc_apply (z : ℂ) : Cc z = star z := rfl

-- mathlib has `Complex.conj_I`, but we work with `star`.
@[simp] lemma star_I' : star (I : ℂ) = -I := by
  simpa [Complex.star_def] using Complex.conj_I

/-- `J_ℂ ∘ C = - C ∘ J_ℂ`. -/
@[simp] lemma Jc_comp_Cc_anticomm :
  (Jc ℂ).comp Cc = - Cc.comp (Jc ℂ) := by
  ext z
  -- `(J ∘ C) z = I • conj z`, `(C ∘ J) z = conj (I • z) = (star I) • conj z = (-I) • conj z`
  -- hence they differ by a minus sign.
  have hI : star (I : ℂ) = -I := star_I'
  -- use `•` (ℂ-scalar on ℂ); Lean rewrites it to `(*)`.
  simp [Jc_apply, Cc_apply, hI, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

/-! A small helper: composition with a fixed `ℝ`-CLM on the codomain. -/

/-- `fderivℝ` commutes with post-composition by a fixed `ℝ`-continuous linear map. -/
lemma fderivR_post (L : W →L[ℝ] V) (f : H → W) (u : H)
  (hf : HasRDerivAt f u (fderivR f u)) :
  fderivR (fun x => L (f x)) u = L.comp (fderivR f u) := by
  -- We use the fact that the real Fréchet derivative is a continuous linear map,
  -- and `HasRDerivAt.comp` on the right. Rename if your snapshot differs.
  have hL : HasRDerivAt (fun y : W => L y) (f u) L := L.hasRDerivAt
  have hcomp := hL.comp u hf
  -- both sides are CLMs; ext on a direction.
  ext v
  simpa [fderivR, ContinuousLinearMap.comp_apply] using (HasRDerivAt.hasFDerivAt hcomp).hasDeriv_linear v

/-! ### Conjugation rules (LaTeX (1)–(3)) -/

section conj_rules
variable (f : H → ℂ) (u : H)
variable (hf : HasRDerivAt f u (fderivR f u))

/-- `D₊(conj f) = C ∘ D₋(f)` (operator form). -/
lemma Dplus_conj_op :
  DplusCLM (fun x => star (f x)) u = (Cc).comp (DminusCLM f u) := by
  -- Real derivative of `conj ∘ f`
  have hDf : fderivR (fun x => star (f x)) u = (Cc).comp (fderivR f u) :=
    fderivR_post (L:=Cc) (f:=f) (u:=u) hf
  -- Push `Aℒ` using `J ∘ C = - C ∘ J`.
  have hA :
    Aℒ (fderivR (fun x => star (f x)) u)
      = - (Cc).comp (Aℒ (fderivR f u)) := by
    ext v
    simp [hDf, Aℒ, ContinuousLinearMap.comp_apply, Jc_apply, Jc_comp_Cc_anticomm]
  -- Unfold `D₊`.
  ext v; simp [DplusCLM, hDf, hA, ContinuousLinearMap.comp_apply, sub_eq_add_neg, smul_add]

/-- `D₋(conj f) = C ∘ D₊(f)` (operator form). -/
lemma Dminus_conj_op :
  DminusCLM (fun x => star (f x)) u = (Cc).comp (DplusCLM f u) := by
  have hDf : fderivR (fun x => star (f x)) u = (Cc).comp (fderivR f u) :=
    fderivR_post (L:=Cc) (f:=f) (u:=u) hf
  have hA :
    Aℒ (fderivR (fun x => star (f x)) u)
      = - (Cc).comp (Aℒ (fderivR f u)) := by
    ext v
    simp [hDf, Aℒ, ContinuousLinearMap.comp_apply, Jc_apply, Jc_comp_Cc_anticomm]
  ext v; simp [DminusCLM, hDf, hA, ContinuousLinearMap.comp_apply, add_comm, add_left_comm,
               add_assoc, smul_add, sub_eq_add_neg]

/-- `∇₊(conj f) = ∇₋ f` and `∇₋(conj f) = ∇₊ f`. -/
lemma grad_conj_swap :
  gradPlus (fun x => star (f x)) u = gradMinus f u
  ∧ gradMinus (fun x => star (f x)) u = gradPlus f u := by
  constructor
  · -- Use the inner-product characterization against `D₊(conj f) = C ∘ D₋ f`
    ext v
    have := Dplus_conj_op (f:=f) (u:=u) hf
    have h1 : DplusCLM (fun x => star (f x)) u v
              = star (DminusCLM f u v) := by
      simpa [ContinuousLinearMap.comp_apply, Cc_apply] using congrArg (fun T => T v) this
    -- `⟪∇₊(conj f), v⟫ = ⟪∇₋ f, v⟫`
    simpa [inner_gradPlus_eq_Dplus, Dminus_eq_inner_gradMinus, inner_conj_symm] using h1
  · -- Symmetric using the `D₋` identity
    ext v
    have := Dminus_conj_op (f:=f) (u:=u) hf
    have h1 : DminusCLM (fun x => star (f x)) u v
              = star (DplusCLM f u v) := by
      simpa [ContinuousLinearMap.comp_apply, Cc_apply] using congrArg (fun T => T v) this
    -- `⟪v, ∇₋(conj f)⟫ = ⟪v, ∇₊ f⟫`
    simpa [Dminus_eq_inner_gradMinus, inner_gradPlus_eq_Dplus, inner_conj_symm] using h1

end conj_rules

/-! ### Algebraic operations (scalar combos & product/quotient) -/

section algebra_ops
variable (f g : H → ℂ) (u : H)
variable (hf : HasRDerivAt f u (fderivR f u))
variable (hg : HasRDerivAt g u (fderivR g u))

/-- Multiplication by a fixed scalar, viewed as an `ℝ`-CLM on `ℂ`. -/
def mulCLM (a : ℂ) : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := fun z => a * z
  , map_add' := by intro x y; simp [mul_add]
  , map_smul' := by intro r z; simp }
, cont := by
    simpa using (continuous_const.mul continuous_id) }

lemma Aℒ_post_mul (a : ℂ) (T : H →L[ℝ] ℂ) :
  Aℒ ((mulCLM a).comp T) = (mulCLM a).comp (Aℒ T) := by
  ext v; simp [Aℒ, ContinuousLinearMap.comp_apply, Jc_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

/-- `D₊(a f) = a • D₊ f` and `D₋(a f) = a • D₋ f` (operator level). -/
lemma Dpm_smul (a : ℂ) :
  DplusCLM (fun x => a * f x) u = (mulCLM a).comp (DplusCLM f u) ∧
  DminusCLM (fun x => a * f x) u = (mulCLM a).comp (DminusCLM f u) := by
  -- First, `Df_{a f} = (mulCLM a) ∘ Df`
  have hDf : fderivR (fun x => a * f x) u = (mulCLM a).comp (fderivR f u) :=
    fderivR_post (L:=mulCLM a) (f:=f) (u:=u) hf
  -- `Aℒ` passes through unchanged for `mulCLM a`
  have hA : Aℒ (fderivR (fun x => a * f x) u) = (mulCLM a).comp (Aℒ (fderivR f u)) := by
    ext v; simp [hDf, Aℒ, ContinuousLinearMap.comp_apply, Jc_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  constructor <;>
  ext v <;>
  simp [DplusCLM, DminusCLM, hDf, hA, ContinuousLinearMap.comp_apply, smul_add, sub_eq_add_neg]

/-- Scalar combination of `∇₊`. -/
lemma gradPlus_scomb (α β : ℂ) :
  gradPlus (fun x => α * f x + β * g x) u
    = (star α) • gradPlus f u + (star β) • gradPlus g u := by
  ext v
  have hα := (Dpm_smul (f:=f) (u:=u) hf α).1
  have hβ := (Dpm_smul (f:=g) (u:=u) hg β).1
  simp [inner_gradPlus_eq_Dplus, ContinuousLinearMap.comp_apply, hα, hβ,
        map_add, mul_add, inner_add_left, inner_smul_left, star_star,
        add_comm, add_left_comm, add_assoc]

/-- Scalar combination of `∇₋`. -/
lemma gradMinus_scomb (α β : ℂ) :
  gradMinus (fun x => α * f x + β * g x) u
    = α • gradMinus f u + β • gradMinus g u := by
  ext v
  have hα := (Dpm_smul (f:=f) (u:=u) hf α).2
  have hβ := (Dpm_smul (f:=g) (u:=u) hg β).2
  simp [Dminus_eq_inner_gradMinus, ContinuousLinearMap.comp_apply, hα, hβ,
        map_add, mul_add, inner_add_right, inner_smul_right,
        add_comm, add_left_comm, add_assoc]

/-- Product rule for Wirtinger gradients. -/
lemma grad_prod :
  gradPlus (fun x => f x * g x) u
    = (star (f u)) • gradPlus g u + (star (g u)) • gradPlus f u
  ∧
  gradMinus (fun x => f x * g x) u
    = (f u) • gradMinus g u + (g u) • gradMinus f u := by
  -- real derivative product rule at the CLM level (rename here if your snapshot differs):
  have hDf :
    fderivR (fun x => f x * g x) u
      = (mulCLM (f u)).comp (fderivR g u) + (mulCLM (g u)).comp (fderivR f u) := by
    -- Replace `PRODUCT RULE NAME HERE` with whatever proves this equality in your project.
    -- Most snapshots expose it as `(hf.mul hg).fderivR` or a sibling. If the name differs,
    -- change this single line.
    exact (fderivR_mul (hf) (hg))  -- ← rename here if needed
  have hA :
    Aℒ (fderivR (fun x => f x * g x) u)
      = (mulCLM (f u)).comp (Aℒ (fderivR g u))
        + (mulCLM (g u)).comp (Aℒ (fderivR f u)) := by
    ext v
    simp [hDf, Aℒ, ContinuousLinearMap.comp_apply, Jc_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, map_add, add_comm, add_left_comm, add_assoc]
  -- D₊
  have hDplus :
    DplusCLM (fun x => f x * g x) u
      = (mulCLM (f u)).comp (DplusCLM g u)
        + (mulCLM (g u)).comp (DplusCLM f u) := by
    ext v; simp [DplusCLM, hDf, hA, ContinuousLinearMap.comp_apply, smul_add, sub_eq_add_neg]
  -- D₋
  have hDminus :
    DminusCLM (fun x => f x * g x) u
      = (mulCLM (f u)).comp (DminusCLM g u)
        + (mulCLM (g u)).comp (DminusCLM f u) := by
    ext v; simp [DminusCLM, hDf, hA, ContinuousLinearMap.comp_apply, smul_add]
  constructor
  · ext v
    simp [inner_gradPlus_eq_Dplus, hDplus, ContinuousLinearMap.comp_apply,
          inner_add_left, inner_smul_left, star_star]
  · ext v
    simp [Dminus_eq_inner_gradMinus, hDminus, ContinuousLinearMap.comp_apply,
          inner_add_right, inner_smul_right]

/-- Reciprocal (on `g u ≠ 0`) and quotient rules. -/
lemma grad_recip_quot (hg0 : g u ≠ 0) :
  gradPlus (fun x => (g x)⁻¹) u = - ((1 / (star (g u))^2) • gradPlus g u)
  ∧
  gradMinus (fun x => (g x)⁻¹) u = - ((1 / (g u)^2) • gradMinus g u)
  ∧
  gradPlus (fun x => f x / g x) u
    = (1 / (star (g u))^2) •
        ((star (g u)) • gradPlus f u - (star (f u)) • gradPlus g u)
  ∧
  gradMinus (fun x => f x / g x) u
    = (1 / (g u)^2) •
        ((g u) • gradMinus f u - (f u) • gradMinus g u) := by
  -- From `1 = g * (1/g)` and the product rules (algebra).
  have hprod := grad_prod (f:=g) (g:=fun x => (g x)⁻¹) (u:=u) hf (hg.inv hg0)
  -- `0 = ∇(g * g⁻¹)` ⇒ solve for the unknown gradients of `g⁻¹`
  have h₊ := hprod.1
  have h₋ := hprod.2
  -- gradients of constant 1 are 0
  have hconst₊ : gradPlus (fun _ : H => (1 : ℂ)) u = 0 := by
    ext v; simp
  have hconst₋ : gradMinus (fun _ : H => (1 : ℂ)) u = 0 := by
    ext v; simp
  -- rewrite the two eqns and solve
  have h₊' :
    (star (g u)) • gradPlus (fun x => (g x)⁻¹) u
      = - (star ((g u)⁻¹)) • gradPlus g u := by
    simpa [hconst₊, one_mul, inv_mul_cancel hg0, star_inv] using h₊
  have h₋' :
    (g u) • gradMinus (fun x => (g x)⁻¹) u
      = - ((g u)⁻¹) • gradMinus g u := by
    simpa [hconst₋, one_mul, inv_mul_cancel hg0] using h₋
  have hrec₊ :
    gradPlus (fun x => (g x)⁻¹) u
      = - ((1 / (star (g u))^2) • gradPlus g u) := by
    have hne : (star (g u)) ≠ 0 := by simpa [star_eq_zero] using congrArg star hg0
    have := congrArg (fun z => (star (g u))⁻¹ • z) h₊'
    -- rewrite to `(1 / (⋯)^2) • …`
    simpa [div_eq_mul_inv, smul_smul, inv_mul_cancel hne, one_smul, star_inv,
           inv_pow, pow_two, mul_comm, mul_left_comm, mul_assoc] using this
  have hrec₋ :
    gradMinus (fun x => (g x)⁻¹) u
      = - ((1 / (g u)^2) • gradMinus g u) := by
    have hne : (g u) ≠ 0 := hg0
    have := congrArg (fun z => (g u)⁻¹ • z) h₋'
    simpa [div_eq_mul_inv, smul_smul, inv_mul_cancel hne, one_smul,
           inv_pow, pow_two, mul_comm, mul_left_comm, mul_assoc] using this
  -- quotient `f/g = f * (g⁻¹)`
  have hq := grad_prod (f:=f) (g:=fun x => (g x)⁻¹) (u:=u) hf (hg.inv hg0)
  constructor
  · exact hrec₊
  constructor
  · exact hrec₋
  constructor
  · simpa [hrec₊, smul_add, add_comm, add_left_comm, add_assoc, div_eq_mul_inv] using hq.1
  · simpa [hrec₋, smul_add, add_comm, add_left_comm, add_assoc, div_eq_mul_inv] using hq.2

end algebra_ops

/-! ### Real and complex gradients -/

section real_complex_grad
variable (f : H → ℂ) (u : H)

/-- If `f` is real-valued at every point, then `∇₊ f = ∇₋ f`. -/
lemma grad_real_eq (hreal : ∀ x, star (f x) = f x) :
  gradPlus f u = gradMinus f u := by
  -- use the conjugation swap with `conj f = f`
  have hfR : HasRDerivAt f u (fderivR f u) := (fderivR_hasDerivAt (f:=f) (u:=u))
  have hswap := (grad_conj_swap (f:=f) (u:=u) hfR)
  -- rewrite `conj f = f` on both sides
  have hfix₊ :
    gradPlus (fun x => star (f x)) u = gradPlus f u := by
    ext v; simp [inner_gradPlus_eq_Dplus, hreal]
  have hfix₋ :
    gradMinus (fun x => star (f x)) u = gradMinus f u := by
    ext v; simp [Dminus_eq_inner_gradMinus, hreal]
  simpa [hfix₊] using hswap.1

/-- Real-derivative identity `Df[u][v] = 2 * Re ⟪∇ℝ f[u], v⟫` for real-valued `f`. -/
lemma real_derivative_formula (hreal : ∀ x, star (f x) = f x) (v : H) :
  fderivR f u v
    = 2 * Complex.re (inner (𝕜 := ℂ) (gradPlus f u) v) := by
  have hgr : gradPlus f u = gradMinus f u := grad_real_eq (f:=f) (u:=u) hreal
  have hsplit := R_split_scalar_point (f:=f) (u:=u) (v:=v)
  -- `⟪v, ∇₊ f⟫ = conj ⟪∇₊ f, v⟫`
  have hz :
    inner (𝕜 := ℂ) v (gradPlus f u)
      = star (inner (𝕜 := ℂ) (gradPlus f u) v) := by
    simpa [inner_conj_symm]
  -- assemble: `Df = z + conj z = 2 * re z`
  have := hsplit
  have := by simpa [hgr, hz] using this
  simpa [two_mul, Complex.re] using this

/-- If `f` is holomorphic at `u` (i.e. `∇₋ f[u] = 0`), then `∇_ℂ f[u] = ∇₊ f[u]`. -/
def gradComplex (f : H → ℂ) (u : H) : H := gradPlus f u
@[simp] lemma gradComplex_eq_gradPlus
  (hol : gradMinus f u = 0) : gradComplex f u = gradPlus f u := rfl

end real_complex_grad

/-! ### Chain rule (general form) -/

section chain_rule
variable (g : H → V) (f : V → ℂ) (u : H)

/-- Explicit derivative hypotheses for the chain rule. -/
variable (hg : HasRDerivAt g u (fderivR g u))
variable (hf : HasRDerivAt f (g u) (fderivR f (g u)))

/-- Upgrade `D₊ g[u]` to a `ℂ`-CLM (we only need it for the adjoint). -/
def DplusCLM_clinear' : H →L[ℂ] V :=
{ toLinearMap :=
  { toFun := fun v => DplusCLM (g) u v
  , map_add' := by intro x y; simp
  , map_smul' := by
      intro a v
      -- show `D₊(a•v) = a•D₊ v` using the `J`-commutation of `D₊`
      set D := DplusCLM (g) u
      have hI : D (I • v) = I • D v := by
        have h0 := congrArg (fun (T : H →L[ℝ] V) => T v)
                      (isCLinearR_Dplus (f:=g) (u:=u))
        simp [ContinuousLinearMap.comp_apply, Jc_apply] at h0
        exact h0.symm
      -- `a = a.re + a.im * I`, use ℝ-linearity.
      have hv := complexSmul_decompose (V:=H) a v
      have hR : D (a • v) = a.re • D v + a.im • D (I • v) := by
        simpa [D.map_add, D.map_smul] using congrArg D hv
      -- Rewrite with a single ℂ-scalar.
      have hR' :
        D (a • v) = (a.re : ℂ) • D v + (a.im : ℂ) • (I • D v) := by
        simpa [Algebra.smul_def, hI, mul_comm, mul_left_comm, mul_assoc] using hR
      have hfact :
        (a.re : ℂ) • D v + (a.im : ℂ) • (I • D v) = a • D v := by
        -- `a.re + a.im * I = a`
        simpa [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc, Complex.re_add_im] using rfl
      simpa [hfact] using hR' }
, cont := (DplusCLM (g) u).continuous }

/-- `D₋ g[u]` is additive and antilinear in the argument (for `conjAdjoint`). -/
lemma Dminus_add_smul :
  (∀ x y, DminusCLM (g) u (x + y)
           = DminusCLM g u x + DminusCLM g u y)
  ∧ (∀ (a : ℂ) x, DminusCLM g u (a • x)
           = (star a) • DminusCLM g u x) := by
  constructor
  · intro x y; simp
  · intro a x
    set D := DminusCLM (g) u
    have hI : D (I • x) = - I • D x := by
      have h0 := congrArg (fun (T : H →L[ℝ] V) => T x)
                    (isALinearR_Dminus (f:=g) (u:=u))
      have h' := congrArg Neg.neg h0
      simpa [ContinuousLinearMap.comp_apply, Jc_apply, neg_neg] using h'.symm
    have hx := complexSmul_decompose (V:=H) a x
    have hR : D (a • x) = a.re • D x + a.im • D (I • x) := by
      simpa [D.map_add, D.map_smul] using congrArg D hx
    -- Turn the `I`-term using `hI`
    have : D (a • x) = (a.re : ℂ) • D x + (-(a.im : ℂ) * I) • D x := by
      have : a.im • D (I • x) = a.im • (- I • D x) := by simpa [hI]
      have : a.im • D (I • x) = (-(a.im : ℂ) * I) • D x := by
        simpa [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc, smul_smul] using this
      simpa [this, Algebra.smul_def, add_comm, add_left_comm, add_assoc] using hR
    -- `(a.re - a.im * I) = star a`
    simpa [Algebra.smul_def, star_eq_re_sub_im, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
      using this

/-- General chain rule for Wirtinger gradients. -/
lemma grad_chain_rule :
  gradPlus (fun x => f (g x)) u
    = (ContinuousLinearMap.adjoint (DplusCLM_clinear' (g:=g) (f:=f) (u:=u) hg hf))
        (gradPlus f (g u))
    + (conjAdjoint (B := fun v => DminusCLM (g) u v)
                   (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).1
                   (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).2
                   (DminusCLM (g) u).continuous)
        (gradMinus f (g u))
  ∧
  gradMinus (fun x => f (g x)) u
    = (conjAdjoint (B := fun v => DminusCLM (g) u v)
                   (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).1
                   (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).2
                   (DminusCLM (g) u).continuous)
        (gradPlus f (g u))
    + (ContinuousLinearMap.adjoint (DplusCLM_clinear' (g:=g) (f:=f) (u:=u) hg hf))
        (gradMinus f (g u)) := by
  classical
  -- shorthands
  set A := DplusCLM (g) u
  set B := DminusCLM (g) u
  set p := gradPlus f (g u)
  set q := gradMinus f (g u)
  have hsplit_f :
    ∀ h, fderivR f (g u) h
          = inner (𝕜 := ℂ) p h + inner (𝕜 := ℂ) h q := by
    intro h; simpa [p, q] using
      (R_split_scalar_point (f:=f) (u:=g u) (v:=h))
  -- D₊ part
  have hDplus :
    ∀ v, DplusCLM (fun x => f (g x)) u v
          = inner (𝕜 := ℂ)
              ((ContinuousLinearMap.adjoint (DplusCLM_clinear' (g:=g) (f:=f) (u:=u) hg hf)) p
               + (conjAdjoint (B := fun y => B y)
                              (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).1
                              (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).2
                              (B).continuous) q)
              v := by
    intro v
    -- start from `Df∘g[u][v] = Df[g u][A v + B v]`
    have : fderivR (fun x => f (g x)) u v
            = inner (𝕜 := ℂ) p (A v + B v) + inner (𝕜 := ℂ) (A v + B v) q := by
      -- `Df∘g = Df[g u] ∘ Dg[u]`, then split `Dg[u] = A + B`
      have := fderivR_post (L:=fderivR f (g u)) (f:=g) (u:=u) hg
      have := congrArg (fun T => T v) this
      simpa [A, B, ContinuousLinearMap.comp_apply, hsplit_f (A v + B v)]
        using this
    -- `(1,0)`-part in `v`
    have t1 : inner (𝕜 := ℂ) p (A v) = inner (𝕜 := ℂ)
          ((ContinuousLinearMap.adjoint (DplusCLM_clinear' (g:=g) (f:=f) (u:=u) hg hf)) p) v := by
      simpa [A, DplusCLM_clinear', inner_adjoint_linear] using
        (inner_adjoint_linear
          (A := DplusCLM_clinear' (g:=g) (f:=f) (u:=u) hg hf) (x := p) (y := v))
    have t4 : inner (𝕜 := ℂ) (B v) q = inner (𝕜 := ℂ)
          ((conjAdjoint (B := fun y => B y)
                         (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).1
                         (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).2
                         (B).continuous) q) v := by
      -- `⟪(B†) q, v⟫ = ⟪B v, q⟫`
      have := inner_conjAdjoint
        (B := fun y : H => B y)
        (h_add := (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).1)
        (h_smul := (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).2)
        (h_cont := (B).continuous) (x := q) (y := v)
      simpa [A, B] using this.symm
    -- split identity previously proven
    have : DplusCLM (fun x => f (g x)) u v
          = inner (𝕜 := ℂ) p (A v) + inner (𝕜 := ℂ) (B v) q := by
      have := R_split_scalar_point (f:=fun x => f (g x)) (u:=u) (v:=v)
      simpa [A, B, hsplit_f (A v + B v), inner_add_left, inner_add_right,
             add_comm, add_left_comm, add_assoc] using this
    -- substitute `t1`, `t4`
    simpa [t1, t4, inner_add_left, add_comm, add_left_comm, add_assoc]
  -- D₋ part
  have hDminus :
    ∀ v, DminusCLM (fun x => f (g x)) u v
          = inner (𝕜 := ℂ) v
              ((conjAdjoint (B := fun y => B y)
                             (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).1
                             (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).2
                             (B).continuous) p
               + (ContinuousLinearMap.adjoint (DplusCLM_clinear' (g:=g) (f:=f) (u:=u) hg hf)) q) := by
    intro v
    -- terms conjugate-linear in `v`: `⟪p, B v⟫` and `⟪A v, q⟫`
    have t2 : inner (𝕜 := ℂ) p (B v)
            = inner (𝕜 := ℂ) v
                ((conjAdjoint (B := fun y => B y)
                               (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).1
                               (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).2
                               (B).continuous) p) := by
      -- from `inner_eq_star_adjoint` + `inner_conj_symm`
      have := inner_eq_star_adjoint
        (B := fun y : H => B y)
        (h_add := (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).1)
        (h_smul := (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).2)
        (h_cont := (B).continuous) (x := p) (y := v)
      -- `⟪p, B v⟫ = ⟪v, (B†) p⟫`
      simpa [A, B, inner_conj_symm] using this.symm
    have t3 : inner (𝕜 := ℂ) (A v) q
            = inner (𝕜 := ℂ) v
                ((ContinuousLinearMap.adjoint (DplusCLM_clinear' (g:=g) (f:=f) (u:=u) hg hf)) q) := by
      have := inner_adjoint_linear
        (A := DplusCLM_clinear' (g:=g) (f:=f) (u:=u) hg hf) (x := q) (y := v)
      -- `⟪A v, q⟫ = ⟪v, A† q⟫`
      simpa [A, DplusCLM_clinear'] using this
    have : DminusCLM (fun x => f (g x)) u v
            = inner (𝕜 := ℂ) v
                ((conjAdjoint (B := fun y => B y)
                               (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).1
                               (Dminus_add_smul (g:=g) (f:=f) (u:=u) hg hf).2
                               (B).continuous) p
                 + (ContinuousLinearMap.adjoint (DplusCLM_clinear' (g:=g) (f:=f) (u:=u) hg hf)) q) := by
      -- keep the `(0,1)`-part `t2 + t3`
      have hsplit := R_split_scalar_point (f:=fun x => f (g x)) (u:=u) (v:=v)
      have hbase :
        fderivR (fun x => f (g x)) u v
          = inner (𝕜 := ℂ) p (A v + B v) + inner (𝕜 := ℂ) (A v + B v) q := by
        have := fderivR_post (L:=fderivR f (g u)) (f:=g) (u:=u) hg
        simpa [A, B, ContinuousLinearMap.comp_apply, hsplit_f (A v + B v)]
          using congrArg (fun T => T v) this
      -- build the `(0,1)` part directly via `t2`, `t3`
      simpa [A, B, t2, t3, inner_add_right, add_comm, add_left_comm, add_assoc]
    simpa using this
  -- Riesz uniqueness for both gradients
  constructor
  · ext v; simpa [inner_add_left] using hDplus v
  · ext v; simpa [inner_add_right] using hDminus v

end chain_rule

/-! ### Useful specializations of the chain rule -/

section chain_special

/-- Inner affine map `g u = A u + b` with `A` ℂ-linear: `∇₊(f∘g) = A† ∇₊ f∘g`, etc. -/
lemma grad_chain_inner_affine
  (A : H →L[ℂ] H) (b : H) (f : H → ℂ) (u : H) :
  gradPlus (fun x => f (A x + b)) u
    = (ContinuousLinearMap.adjoint A) (gradPlus f (A u + b))
  ∧
  gradMinus (fun x => f (A x + b)) u
    = (ContinuousLinearMap.adjoint A) (gradMinus f (A u + b)) := by
  -- Apply the general chain rule with g = x ↦ A x + b.
  -- Here D₊ g = A, D₋ g = 0.
  have hg : HasRDerivAt (fun x => A x + b) u (fderivR (fun x => A x + b) u) :=
    (fderivR_hasDerivAt (f:=fun x => A x + b) (u:=u))
  have hf : HasRDerivAt f (A u + b) (fderivR f (A u + b)) :=
    (fderivR_hasDerivAt (f:=f) (u:=A u + b))
  have hDplus :
    DplusCLM_clinear' (g:=fun x => A x + b) (f:=f) (u:=u) hg hf = A := by
    ext v; simp [DplusCLM, fderivR, Aℒ, Jc_apply, ContinuousLinearMap.comp_apply]
  have hDminus :
    (conjAdjoint (B := fun v => DminusCLM (fun x => A x + b) u v)
        (by intro x y; simp) (by intro a x; simp) ((DminusCLM (fun x => A x + b) u).continuous))
      = (0 : H → H) := by
    funext v; simp [DminusCLM, fderivR, Aℒ, Jc_apply, ContinuousLinearMap.comp_apply]
  have := grad_chain_rule (g:=fun x => A x + b) (f:=f) (u:=u) hg hf
  constructor
  · simpa [hDplus, hDminus, ContinuousLinearMap.comp_apply] using this.1
  · simpa [hDplus, hDminus, ContinuousLinearMap.comp_apply] using this.2

/-- Outer scalar function specialization with `V = ℂ`. -/
lemma grad_chain_outer_scalar (g : H → ℂ) (f : ℂ → ℂ) (u : H) :
  gradPlus (fun x => f (g x)) u
    = (gradPlus f (g u)) • (gradPlus g u) + (star (gradMinus f (g u))) • (gradMinus g u)
  ∧
  gradMinus (fun x => f (g x)) u
    = (star (gradPlus f (g u))) • (gradMinus g u) + (gradMinus f (g u)) • (gradPlus g u) := by
  -- For `A := D₊ g`, `A†[c] = c • ∇₊ g`, and `(B†)[c] = (star c) • ∇₋ g`.
  have hg : HasRDerivAt g u (fderivR g u) := (fderivR_hasDerivAt (f:=g) (u:=u))
  have hf : HasRDerivAt f (g u) (fderivR f (g u)) :=
    (fderivR_hasDerivAt (f:=f) (u:=g u))
  have hA :
    ∀ c, (ContinuousLinearMap.adjoint (DplusCLM_c_linear (f:=g) (u:=u))) c
          = c • gradPlus g u := by
    intro c
    ext v
    -- `⟪A† c, v⟫ = ⟪c, A v⟫ = star c * D₊g v = ⟪c • ∇₊g, v⟫`
    simp [inner_adjoint_linear, inner_gradPlus_eq_Dplus, inner_smul_left]
  have hB :
    ∀ c, (conjAdjoint (B := fun y => DminusCLM (g) u y)
            (by intro x y; simp) (by intro a x; simp [DminusCLM_star_c_linear_apply])
            (DminusCLM (g) u).continuous) c
          = (star c) • gradMinus g u := by
    intro c
    ext v
    -- `⟪(B†) c, v⟫ = ⟪c, B v⟫ = star c * D₋g v = ⟪(star c) • ∇₋g, v⟫`
    simp [inner_eq_star_adjoint, Dminus_eq_inner_gradMinus, inner_smul_right, inner_smul_left,
          inner_conj_symm]
  -- Plug into the general chain rule with `V = ℂ`
  have := grad_chain_rule (g:=g) (f:=f) (u:=u) hg hf
  constructor
  · -- `∇₊`
    simpa [hA _, hB _, smul_add, add_comm, add_left_comm, add_assoc] using this.1
  · -- `∇₋`
    simpa [hA _, hB _, smul_add, add_comm, add_left_comm, add_assoc] using this.2

end chain_special

/-! ### Unitary transport (derivative & gradient levels) -/

section unitary_transport
variable {Ĥ : Type _} [NormedAddCommGroup Ĥ] [InnerProductSpace ℂ Ĥ] [CompleteSpace Ĥ]

/-- Transport of `D₊/D₋` under a unitary `U : H ≃ₗᵢ[ℂ] Ĥ`. -/
lemma Dpm_unitary (U : H ≃ₗᵢ[ℂ] Ĥ) (f : H → ℂ) (u : H) :
  DplusCLM (H:=Ĥ) (fun û => f (U.symm û)) (U u) = (DplusCLM (f) u).comp (U.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  ∧
  DminusCLM (H:=Ĥ) (fun û => f (U.symm û)) (U u) = (DminusCLM (f) u).comp (U.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  constructor <;> ext v <;>
  simp [DplusCLM, DminusCLM, Aℒ, Jc_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.comp_apply,
    LinearIsometry.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- Gradient transport under a unitary `U : H ≃ₗᵢ[ℂ] Ĥ`. -/
lemma grad_unitary (U : H ≃ₗᵢ[ℂ] Ĥ) (f : H → ℂ) (u : H) :
  gradPlus (H:=Ĥ) (fun û => f (U.symm û)) (U u) = U (gradPlus f u)
  ∧
  gradMinus (H:=Ĥ) (fun û => f (U.symm û)) (U u) = U (gradMinus f u) := by
  constructor
  · -- `∇₊`
    ext vhat
    have hD := (Dpm_unitary (U:=U) (f:=f) (u:=u)).1
    have : inner (𝕜 := ℂ) (gradPlus (H:=Ĥ) (fun û => f (U.symm û)) (U u)) vhat
            = inner (𝕜 := ℂ) (gradPlus f u) (U.symm vhat) := by
      simpa [inner_gradPlus_eq_Dplus, ContinuousLinearMap.comp_apply]
        using congrArg (fun T => T vhat) hD
    simpa [LinearIsometry.inner_map_isometry] using this
  · -- `∇₋`
    ext vhat
    have hD := (Dpm_unitary (U:=U) (f:=f) (u:=u)).2
    have : inner (𝕜 := ℂ) vhat
              (gradMinus (H:=Ĥ) (fun û => f (U.symm û)) (U u))
            = inner (𝕜 := ℂ) (U.symm vhat) (gradMinus f u) := by
      simpa [Dminus_eq_inner_gradMinus, ContinuousLinearMap.comp_apply]
        using congrArg (fun T => T vhat) hD
    simpa [LinearIsometry.inner_map_isometry] using this.symm

end unitary_transport

end rules_of_operation



end Wirtinger
