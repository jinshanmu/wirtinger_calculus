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

/-! ## Conjugation Rules (W = ℂ) -/
section conjugation
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Complex conjugation as a continuous `ℝ`-linear map on `ℂ`. -/
def conjCLM : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := fun z => star z
  , map_add' := by intro x y; simp
  , map_smul' := by
      intro r z
      -- `(r : ℝ) • z = (r : ℂ) * z` and `star` respects multiplication.
      simp [Algebra.smul_def] }
, cont := continuous_conj }

@[simp] lemma conjCLM_apply (z : ℂ) : conjCLM z = star z := rfl

/-- `conj ∘ J = - J ∘ conj` on `ℂ`. -/
@[simp] lemma conjCLM_comp_Jc :
    conjCLM.comp (Jc ℂ) = - (Jc ℂ).comp conjCLM := by
  ext z
  change star (I * z) = -(I * star z)
  calc
    star (I * z) = star z * star I := by simp [star_mul]
    _ = star z * (-I) := by simp
    _ = -(star z * I) := by simp [mul_neg]
    _ = -(I * star z) := by simp [mul_comm]

/-- `J ∘ conj = - conj ∘ J` on `ℂ`. -/
@[simp] lemma Jc_comp_conjCLM :
    (Jc ℂ).comp conjCLM = - conjCLM.comp (Jc ℂ) := by
  ext z
  change I * star z = - star (I * z)
  have h : star (I * z) = -(I * star z) := by
    calc
      star (I * z) = star z * star I := by simp [star_mul]
      _ = star z * (-I) := by simp
      _ = -(star z * I) := by simp [mul_neg]
      _ = -(I * star z) := by simp [mul_comm]
  simp [h]

/-- Chain rule for conjugation: `Df̄[u] = conjCLM ∘ Df[u]`. -/
lemma fderivR_conj_of_hasDeriv
  {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) :
  fderivR (fun x => star (f x)) u = conjCLM.comp D := by
  -- View `x ↦ star (f x)` as `(⇑conjCLM) ∘ f` and apply the chain rule.
  change fderiv ℝ ((⇑conjCLM) ∘ f) u = conjCLM.comp D
  simpa [Function.comp, HasRDerivAt, fderivR]
    using (((conjCLM).hasFDerivAt).comp u hf).fderiv

/-- Operator identity: `D₊(f̄)[u] = conjCLM ∘ D₋ f[u]`. -/
lemma Dplus_conj_op
  {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) :
  DplusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u
    = conjCLM.comp (DminusCLM (H:=H) (W:=ℂ) f u) := by
  have hD : fderivR (H:=H) (W:=ℂ) f u = D := by
    simpa [HasRDerivAt, fderivR] using hf.fderiv
  have hE : fderivR (H:=H) (W:=ℂ) (fun x => star (f x)) u = conjCLM.comp D :=
    fderivR_conj_of_hasDeriv (H:=H) (u:=u) hf
  have hA :
      Aℒ (H:=H) (W:=ℂ) (conjCLM.comp D)
        = - (conjCLM.comp (Aℒ (H:=H) (W:=ℂ) D)) := by
    -- Pointwise: `J ∘ conj = - conj ∘ J`.
    ext v
    simp [Aℒ, ContinuousLinearMap.comp_apply]
  -- Unfold and rewrite deterministically (no heavy `simp`).
  unfold DplusCLM
  rw [hE, hE, hA]
  -- (D̄ − (−Ā)) = D̄ + Ā
  have : (1 / 2 : ℝ) • (conjCLM.comp D + conjCLM.comp (Aℒ (H:=H) (W:=ℂ) D))
        = conjCLM.comp ((1 / 2 : ℝ) • (D + Aℒ (H:=H) (W:=ℂ) D)) := by
    simp [ContinuousLinearMap.comp_add, smul_add, ContinuousLinearMap.comp_smul]
  simpa [DminusCLM, hD] using this.symm

/-- Operator identity: `D₋(f̄)[u] = conjCLM ∘ D₊ f[u]`. -/
lemma Dminus_conj_op
  {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) :
  DminusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u
    = conjCLM.comp (DplusCLM (H:=H) (W:=ℂ) f u) := by
  have hD : fderivR (H:=H) (W:=ℂ) f u = D := by
    simpa [HasRDerivAt, fderivR] using hf.fderiv
  have hE : fderivR (H:=H) (W:=ℂ) (fun x => star (f x)) u = conjCLM.comp D :=
    fderivR_conj_of_hasDeriv (H:=H) (u:=u) hf
  have hA :
      Aℒ (H:=H) (W:=ℂ) (conjCLM.comp D)
        = - (conjCLM.comp (Aℒ (H:=H) (W:=ℂ) D)) := by
    ext v
    simp [Aℒ, ContinuousLinearMap.comp_apply]
  unfold DminusCLM
  rw [hE, hE, hA]
  -- (D̄ + (−Ā)) = D̄ − Ā
  have : (1 / 2 : ℝ) • (conjCLM.comp D - conjCLM.comp (Aℒ (H:=H) (W:=ℂ) D))
        = conjCLM.comp ((1 / 2 : ℝ) • (D - Aℒ (H:=H) (W:=ℂ) D)) := by
    simp [ContinuousLinearMap.comp_sub, smul_sub, ContinuousLinearMap.comp_smul]
  simpa [DplusCLM, hD] using this.symm

/-- Directional form: `D₊(f̄)[u][v] = overline (D₋ f[u][v])`. -/
@[simp] lemma Dplus_conj_dir
  {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) (v : H) :
  DplusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u v
    = star (DminusCLM (H:=H) (W:=ℂ) f u v) := by
  have := congrArg (fun (T : H →L[ℝ] ℂ) => T v) (Dplus_conj_op (H:=H) (u:=u) hf)
  simpa [conjCLM_apply] using this

/-- Directional form: `D₋(f̄)[u][v] = overline (D₊ f[u][v])`. -/
@[simp] lemma Dminus_conj_dir
  {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) (v : H) :
  DminusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u v
    = star (DplusCLM (H:=H) (W:=ℂ) f u v) := by
  have := congrArg (fun (T : H →L[ℝ] ℂ) => T v) (Dminus_conj_op (H:=H) (u:=u) hf)
  simpa [conjCLM_apply] using this

/-- Gradient identity: `∇₊(f̄)[u] = ∇₋ f[u]`. -/
lemma gradPlus_conj_eq_gradMinus
  [CompleteSpace H] {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) :
  gradPlus (H:=H) (fun x => star (f x)) u = gradMinus (H:=H) f u := by
  classical
  -- Compare the Riesz representatives by testing against arbitrary `v`.
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  -- ⟪∇₊(f̄), v⟫ = D₊(f̄)[v]
  have h₁ :
      inner (𝕜:=ℂ) (gradPlus (H:=H) (fun x => star (f x)) u) v
        = DplusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u v :=
    inner_gradPlus_eq_Dplus (H:=H) (f:=fun x => star (f x)) (u:=u) (v:=v)
  -- D₊(f̄)[v] = star (D₋ f[v])
  have h₂ := Dplus_conj_dir (H:=H) (u:=u) (D:=D) hf v
  -- rewrite RHS via the definition of ∇₋:
  have h₃ :
      inner (𝕜:=ℂ) (gradPlus (H:=H) (fun x => star (f x)) u) v
        = star (DminusCLM (H:=H) (W:=ℂ) f u v) := by
    simpa [h₂] using h₁
  have h₄ :
      DminusCLM (H:=H) (W:=ℂ) f u v
        = inner (𝕜:=ℂ) v (gradMinus (H:=H) f u) :=
    Dminus_eq_inner_gradMinus (H:=H) (f:=f) (u:=u) (v:=v)
  -- Turn `star ⟪v, ∇₋ f⟫` into `⟪∇₋ f, v⟫` using `inner_conj_symm`.
  have hflip : inner (𝕜:=ℂ) (gradMinus (H:=H) f u) v
                = star (inner (𝕜:=ℂ) v (gradMinus (H:=H) f u)) :=
    inner_conj_symm _ _
  -- Replace the RHS in `h₃` using `h₄`, then use `hflip` backwards.
  have h₅ := by
    simpa [h₄] using h₃
  -- `h₅ : inner (∇₊(f̄)) v = star ⟪v, ∇₋ f⟫`. Rewrite RHS to `⟪∇₋ f, v⟫`.
  rw [← hflip] at h₅
  exact h₅

/-- Gradient identity: `∇₋(f̄)[u] = ∇₊ f[u]`. -/
lemma gradMinus_conj_eq_gradPlus
  [CompleteSpace H] {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) :
  gradMinus (H:=H) (fun x => star (f x)) u = gradPlus (H:=H) f u := by
  classical
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  -- Start from ⟪v, ∇₋(f̄)⟫.
  have hL :
      inner (𝕜:=ℂ) v (gradMinus (H:=H) (fun x => star (f x)) u)
        = DminusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u v :=
    (Dminus_eq_inner_gradMinus (H:=H) (f:=fun x => star (f x)) (u:=u) (v:=v)).symm
  -- D₋(f̄)[v] = star (D₊ f[v]).
  have hdir := Dminus_conj_dir (H:=H) (u:=u) (D:=D) hf v
  -- And ⟪∇₊ f, v⟫ = D₊ f[v].
  have hplus :
      DplusCLM (H:=H) (W:=ℂ) f u v
        = inner (𝕜:=ℂ) (gradPlus (H:=H) f u) v :=
    (inner_gradPlus_eq_Dplus (H:=H) (f:=f) (u:=u) (v:=v)).symm
  -- Combine the three equalities.
  have : inner (𝕜:=ℂ) v (gradMinus (H:=H) (fun x => star (f x)) u)
        = star (inner (𝕜:=ℂ) (gradPlus (H:=H) f u) v) := by
    simpa [hplus] using (hL.trans hdir)
  -- Now use `inner_conj_symm` to flip the arguments on the RHS.
  simpa [inner_conj_symm] using this

end conjugation

end Wirtinger
