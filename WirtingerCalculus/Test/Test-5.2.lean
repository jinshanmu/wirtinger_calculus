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
abbrev fderivR (f : H → W) (u : H) : H →L[ℝ] W := fderiv ℝ f u

/-- The continuous `ℝ`-linear map `t ↦ t • v`. -/
def lineCLM (v : H) : ℝ →L[ℝ] H := (1 : ℝ →L[ℝ] ℝ).smulRight v

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
lemma star_eq_re_sub_im (a : ℂ) :
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
lemma Jc_comp_Jc (V : Type _) [NormedAddCommGroup V] [NormedSpace ℂ V] :
    (Jc V).comp (Jc V) = - (ContinuousLinearMap.id ℝ V) := by
  ext v; simp [ContinuousLinearMap.comp_apply, Jc_apply, smul_smul, Complex.I_mul_I]

@[simp] lemma Jc_comp_Jc_apply (V : Type _) [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) :
    ((Jc V).comp (Jc V)) v = - v := by
  simp [Jc_comp_Jc V]

abbrev Jc_H : H →L[ℝ] H := Jc H
abbrev Jc_W : W →L[ℝ] W := Jc W

/-- The anti-twist operator `Aℒ(T) = Jc_W ∘ T ∘ Jc_H`. -/
def Aℒ (T : H →L[ℝ] W) : H →L[ℝ] W := (Jc_W).comp (T.comp Jc_H)

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
lemma inner_gradPlus_eq_Dplus (f : H → ℂ) (u v : H) :
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
lemma inner_adjoint_linear (A : H →L[ℂ] W) (x : W) (y : H) :
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
lemma gateaux_at_zero_eq (f : H → W) (u v : H) (D : H →L[ℝ] W)
    (hf : HasRDerivAt f u D) :
    deriv (fun t : ℝ => f (u + t • v)) 0 = D v :=
  real_directional_deriv_eq (f:=f) (u:=u) (v:=v) (D:=D) hf

/-- Pointwise `ℂ`-linearity of `D₊`. -/
lemma Dplus_comm_J_point (f : H → W) (u v : H) :
    (DplusCLM (H:=H) (W:=W) f u) (J_H v)
      = (J_W) ((DplusCLM (H:=H) (W:=W) f u) v) := by
  have h := (congrArg (fun (T : H →L[ℝ] W) => T v)
              (isCLinearR_Dplus (H:=H) (W:=W) f u)).symm
  simp [ContinuousLinearMap.comp_apply] at h
  exact h

/-- Pointwise `ℂ`-antilinearity of `D₋`. -/
lemma Dminus_anticomm_J_point (f : H → W) (u v : H) :
    (DminusCLM (H:=H) (W:=W) f u) (J_H v)
      = - (J_W) ((DminusCLM (H:=H) (W:=W) f u) v) := by
  have h := congrArg (fun (T : H →L[ℝ] W) => T v)
              (isALinearR_Dminus (H:=H) (W:=W) f u)
  have h' := h.symm
  -- negate both sides, then simplify
  have h'' := congrArg Neg.neg h'
  simp [ContinuousLinearMap.comp_apply, neg_neg] at h''
  exact h''

/-- Pointwise Wirtinger split. -/
lemma R_split_point (f : H → W) (u v : H) :
    fderivR (H:=H) (W:=W) f u v
      = DplusCLM (H:=H) (W:=W) f u v + DminusCLM (H:=H) (W:=W) f u v :=
  fderivR_apply_split (H:=H) (W:=W) f u v

/-- Riesz identity for `D₊`. -/
lemma riesz_plus_point [CompleteSpace H] (f : H → ℂ) (u v : H) :
    DplusCLM (H:=H) (W:=ℂ) f u v
      = inner (𝕜 := ℂ) (gradPlus f u) v :=
  (inner_gradPlus_eq_Dplus (f:=f) (u:=u) (v:=v)).symm

/-- Riesz identity for `D₋`. -/
lemma riesz_minus_point [CompleteSpace H] (f : H → ℂ) (u v : H) :
    DminusCLM (H:=H) (W:=ℂ) f u v
      = inner (𝕜 := ℂ) v (gradMinus f u) :=
  Dminus_eq_inner_gradMinus (f:=f) (u:=u) (v:=v)

/-- Wirtinger split for scalar functions using gradients. -/
lemma R_split_scalar_point [CompleteSpace H] (f : H → ℂ) (u v : H) :
    fderivR (H:=H) (W:=ℂ) f u v
      = inner (𝕜 := ℂ) (gradPlus f u) v
        + inner (𝕜 := ℂ) v (gradMinus f u) :=
  fderivR_apply_split_grad (f:=f) (u:=u) (v:=v)

/-- Standard Hermitian adjoint identity. -/
lemma adjoint_linear_eq
  [CompleteSpace H] [CompleteSpace W]
  (A : H →L[ℂ] W) (x : W) (y : H) :
  inner (𝕜 := ℂ) x (A y) = inner (𝕜 := ℂ) ((ContinuousLinearMap.adjoint A) x) y := by
  simp [inner_adjoint_linear]

/-- Antilinear adjoint identity. -/
lemma adjoint_antilinear_star
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

/-- `conj ∘ J = - J ∘ conj` on `ℂ`.  (Not a simp lemma to avoid loops.) -/
lemma conjCLM_comp_Jc :
    conjCLM.comp (Jc ℂ) = - (Jc ℂ).comp conjCLM := by
  ext z
  change star (I * z) = -(I * star z)
  calc
    star (I * z) = star z * star I := by simp [star_mul]
    _ = star z * (-I) := by simp
    _ = -(star z * I) := by simp [mul_neg]
    _ = -(I * star z) := by simp [mul_comm]

/-- `J ∘ conj = - conj ∘ J` on `ℂ`.  (Not a simp lemma to avoid loops.) -/
lemma Jc_comp_conjCLM :
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
  classical
  -- Work with `fderivR` and also the normalized `starRingEnd` form.
  have hE : fderivR (H:=H) (W:=ℂ) (fun x => star (f x)) u = conjCLM.comp D :=
    fderivR_conj_of_hasDeriv (H:=H) (u:=u) hf
  have hE_star :
      fderiv ℝ (fun x => (starRingEnd ℂ) (f x)) u = conjCLM.comp D := by
    have hE' : fderiv ℝ (fun x => star (f x)) u = conjCLM.comp D := by
      simpa [fderivR] using hE
    simpa using hE'
  have hDℝ : fderiv ℝ f u = D := hf.fderiv
  -- `Aℒ` pushes through `conjCLM` with a minus sign.
  have hA :
      Aℒ (H:=H) (W:=ℂ) (conjCLM.comp D)
        = - (conjCLM.comp (Aℒ (H:=H) (W:=ℂ) D)) := by
    ext v; simp [Aℒ, ContinuousLinearMap.comp_apply]
  have hA' :
      Jc_W.comp ((conjCLM.comp D).comp Jc_H)
        = - conjCLM.comp (Jc_W.comp (D.comp Jc_H)) := by
    simpa [Aℒ] using hA
  unfold DplusCLM
  calc
    (1 / 2 : ℝ) •
        ( fderiv ℝ (fun x => (starRingEnd ℂ) (f x)) u
          - Jc_W.comp ((fderiv ℝ (fun x => (starRingEnd ℂ) (f x)) u).comp Jc_H) )
        = (1 / 2 : ℝ) •
            ( (conjCLM.comp D) - Jc_W.comp ((conjCLM.comp D).comp Jc_H) ) := by
          simp [hE_star]
    _   = (1 / 2 : ℝ) •
            ( conjCLM.comp D + conjCLM.comp (Jc_W.comp (D.comp Jc_H)) ) := by
          simp [hA', sub_eq_add_neg]
    _   = conjCLM.comp ((1 / 2 : ℝ) • (D + Jc_W.comp (D.comp Jc_H))) := by
          simp [ContinuousLinearMap.comp_add]
    _   = conjCLM.comp ((1 / 2 : ℝ) • (D + Aℒ (H:=H) (W:=ℂ) D)) := by
          simp [Aℒ]
    _   = conjCLM.comp (DminusCLM (H:=H) (W:=ℂ) f u) := by
          simp [DminusCLM, fderivR, hDℝ]

/-- Operator identity: `D₋(f̄)[u] = conjCLM ∘ D₊ f[u]`. -/
lemma Dminus_conj_op
  {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) :
  DminusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u
    = conjCLM.comp (DplusCLM (H:=H) (W:=ℂ) f u) := by
  classical
  have hE : fderivR (H:=H) (W:=ℂ) (fun x => star (f x)) u = conjCLM.comp D :=
    fderivR_conj_of_hasDeriv (H:=H) (u:=u) hf
  have hE_star :
      fderiv ℝ (fun x => (starRingEnd ℂ) (f x)) u = conjCLM.comp D := by
    have hE' : fderiv ℝ (fun x => star (f x)) u = conjCLM.comp D := by
      simpa [fderivR] using hE
    simpa using hE'
  have hDℝ : fderiv ℝ f u = D := hf.fderiv
  have hA :
      Aℒ (H:=H) (W:=ℂ) (conjCLM.comp D)
        = - (conjCLM.comp (Aℒ (H:=H) (W:=ℂ) D)) := by
    ext v; simp [Aℒ, ContinuousLinearMap.comp_apply]
  have hA' :
      Jc_W.comp ((conjCLM.comp D).comp Jc_H)
        = - conjCLM.comp (Jc_W.comp (D.comp Jc_H)) := by
    simpa [Aℒ] using hA
  unfold DminusCLM
  calc
    (1 / 2 : ℝ) •
        ( fderiv ℝ (fun x => (starRingEnd ℂ) (f x)) u
          + Jc_W.comp ((fderiv ℝ (fun x => (starRingEnd ℂ) (f x)) u).comp Jc_H) )
        = (1 / 2 : ℝ) •
            ( (conjCLM.comp D) + Jc_W.comp ((conjCLM.comp D).comp Jc_H) ) := by
          simp [hE_star]
    _   = (1 / 2 : ℝ) •
            ( (conjCLM.comp D) - conjCLM.comp (Jc_W.comp (D.comp Jc_H)) ) := by
          simp [hA', sub_eq_add_neg]
    _   = conjCLM.comp ((1 / 2 : ℝ) • (D - Jc_W.comp (D.comp Jc_H))) := by
          simp [ContinuousLinearMap.comp_sub]
    _   = conjCLM.comp ((1 / 2 : ℝ) • (D - Aℒ (H:=H) (W:=ℂ) D)) := by
          simp [Aℒ]
    _   = conjCLM.comp (DplusCLM (H:=H) (W:=ℂ) f u) := by
          simp [DplusCLM, fderivR, hDℝ]

/-- Directional form: `D₊(f̄)[u][v] = overline (D₋ f[u][v])`. -/
lemma Dplus_conj_dir
  {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) (v : H) :
  DplusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u v
    = star (DminusCLM (H:=H) (W:=ℂ) f u v) := by
  have h := congrArg (fun (T : H →L[ℝ] ℂ) => T v)
                      (Dplus_conj_op (H:=H) (u:=u) (D:=D) hf)
  simp [conjCLM_apply] at h
  exact h

/-- Directional form: `D₋(f̄)[u][v] = overline (D₊ f[u][v])`. -/
lemma Dminus_conj_dir
  {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) (v : H) :
  DminusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u v
    = star (DplusCLM (H:=H) (W:=ℂ) f u v) := by
  have h := congrArg (fun (T : H →L[ℝ] ℂ) => T v)
                      (Dminus_conj_op (H:=H) (u:=u) (D:=D) hf)
  simp [conjCLM_apply] at h
  exact h

/-- Gradient identity: `∇₊(f̄)[u] = ∇₋ f[u]`. -/
lemma gradPlus_conj_eq_gradMinus
  [CompleteSpace H] {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) :
  gradPlus (H:=H) (fun x => star (f x)) u = gradMinus (H:=H) f u := by
  classical
  -- compare in the dual, then evaluate at `v`
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  -- left side at the dual
  have h1L :
      (InnerProductSpace.toDual ℂ H)
        (gradPlus (H:=H) (fun x => star (f x)) u)
      = DplusCLM_c_linear (H:=H) (fun x => star (f x)) u := by
    convert
      (LinearIsometryEquiv.apply_symm_apply
        (InnerProductSpace.toDual ℂ H)
        (DplusCLM_c_linear (H:=H) (fun x => star (f x)) u)) using 1
  -- right side at the dual
  have h1R :
      (InnerProductSpace.toDual ℂ H)
        (gradMinus (H:=H) f u)
      = DminusCLM_star_c_linear (H:=H) f u := by
    convert
      (LinearIsometryEquiv.apply_symm_apply
        (InnerProductSpace.toDual ℂ H)
        (DminusCLM_star_c_linear (H:=H) f u)) using 1
  -- stitch the chain
  calc
    ((InnerProductSpace.toDual ℂ H)
      (gradPlus (H:=H) (fun x => star (f x)) u)) v
        = (DplusCLM_c_linear (H:=H) (fun x => star (f x)) u) v := by
          exact congrArg (fun T : H →L[ℂ] ℂ => T v) h1L
    _   = DplusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u v := by
          simp [DplusCLM_c_linear_apply]
    _   = star (DminusCLM (H:=H) (W:=ℂ) f u v) := Dplus_conj_dir (H:=H) (u:=u) (D:=D) hf v
    _   = ((InnerProductSpace.toDual ℂ H)
            (gradMinus (H:=H) f u)) v := by
          simp [h1R]

/-- Gradient identity: `∇₋(f̄)[u] = ∇₊ f[u]`. -/
lemma gradMinus_conj_eq_gradPlus
  [CompleteSpace H] {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) :
  gradMinus (H:=H) (fun x => star (f x)) u = gradPlus (H:=H) f u := by
  classical
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  -- left side at the dual
  have h1L :
      (InnerProductSpace.toDual ℂ H)
        (gradMinus (H:=H) (fun x => star (f x)) u)
      = DminusCLM_star_c_linear (H:=H) (fun x => star (f x)) u := by
    convert
      (LinearIsometryEquiv.apply_symm_apply
        (InnerProductSpace.toDual ℂ H)
        (DminusCLM_star_c_linear (H:=H) (fun x => star (f x)) u)) using 1
  -- right side at the dual
  have h1R :
      (InnerProductSpace.toDual ℂ H)
        (gradPlus (H:=H) f u)
      = DplusCLM_c_linear (H:=H) f u := by
    convert
      (LinearIsometryEquiv.apply_symm_apply
        (InnerProductSpace.toDual ℂ H)
        (DplusCLM_c_linear (H:=H) f u)) using 1
  -- stitch the chain
  calc
    ((InnerProductSpace.toDual ℂ H)
      (gradMinus (H:=H) (fun x => star (f x)) u)) v
        = (DminusCLM_star_c_linear (H:=H) (fun x => star (f x)) u) v := by
          exact congrArg (fun T : H →L[ℂ] ℂ => T v) h1L
    _   = star (DminusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u v) := by
          simp [DminusCLM_star_c_linear_apply]
    _   = star (star (DplusCLM (H:=H) (W:=ℂ) f u v)) := by
          exact congrArg star (Dminus_conj_dir (H:=H) (u:=u) (D:=D) hf v)
    _   = DplusCLM (H:=H) (W:=ℂ) f u v := by simp
    _   = ((InnerProductSpace.toDual ℂ H)
            (gradPlus (H:=H) f u)) v := by
          simp [h1R]

end conjugation

/-! ## Algebraic Operations (W = ℂ) -/
section algebraic_ops
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### A tiny helper: left-multiplication by a fixed complex number as an ℝ-CLM -/
/-- `ℂ`-left multiplication by a fixed `c` as a continuous `ℝ`-linear map. -/
def mulLeftCLM (c : ℂ) : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := fun z => c * z
  , map_add' := by intro x y; simp [mul_add]
  , map_smul' := by
      intro r z
      simp [Algebra.smul_def, mul_comm, mul_left_comm] }
, cont := by simpa using (continuous_const.mul continuous_id) }

@[simp] lemma mulLeftCLM_apply (c z : ℂ) : mulLeftCLM c z = c * z := rfl

/-- `Aℒ` commutes with fixed complex left multiplication on `ℂ`. -/
@[simp] lemma Aℒ_comp_mulLeftCLM (T : H →L[ℝ] ℂ) (c : ℂ) :
    Aℒ (H:=H) (W:=ℂ) ((mulLeftCLM c).comp T)
  = (mulLeftCLM c).comp (Aℒ (H:=H) (W:=ℂ) T) := by
  ext v; simp [Aℒ, ContinuousLinearMap.comp_apply, Jc_apply, mul_left_comm]

/-! #### New basic algebra for `Aℒ` and constants (helps `simp`) -/

@[simp] lemma Aℒ_add (T S : H →L[ℝ] ℂ) :
    Aℒ (H:=H) (W:=ℂ) (T + S) = Aℒ (H:=H) (W:=ℂ) T + Aℒ (H:=H) (W:=ℂ) S := by
  ext v; simp [Aℒ, ContinuousLinearMap.comp_apply]

@[simp] lemma Aℒ_sub (T S : H →L[ℝ] ℂ) :
    Aℒ (H:=H) (W:=ℂ) (T - S) = Aℒ (H:=H) (W:=ℂ) T - Aℒ (H:=H) (W:=ℂ) S := by
  ext v; simp [Aℒ]

@[simp] lemma Aℒ_smul_real (c : ℝ) (T : H →L[ℝ] ℂ) :
    Aℒ (H:=H) (W:=ℂ) (c • T) = c • Aℒ (H:=H) (W:=ℂ) T := by
  ext v; simp [Aℒ]

@[simp] lemma mulLeftCLM_comp_eq_smul (c : ℂ) (D : H →L[ℝ] ℂ) :
    (mulLeftCLM c).comp D = c • D := by
  ext v; simp [mulLeftCLM_apply, ContinuousLinearMap.smul_apply]

/-- `Aℒ` also respects `ℂ`-scalar multiplication on maps to `ℂ`. -/
@[simp] lemma Aℒ_smul_complex (c : ℂ) (T : H →L[ℝ] ℂ) :
    Aℒ (H:=H) (W:=ℂ) (c • T) = c • Aℒ (H:=H) (W:=ℂ) T := by
  simpa [mulLeftCLM_comp_eq_smul] using
    (Aℒ_comp_mulLeftCLM (H:=H) (T:=T) (c:=c))

/-! ### Linearity in the function: sums and constant complex multiples -/

/-- `fderivR` of a sum. -/
lemma fderivR_add
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  fderivR (H:=H) (W:=ℂ) (fun x => f x + g x) u = Df + Dg := by
  simpa [HasRDerivAt, fderivR] using ((hf.add hg).fderiv)

/-- `fderivR` of a fixed complex multiple. -/
lemma fderivR_const_mul
  {f : H → ℂ} {u : H} {Df : H →L[ℝ] ℂ} (c : ℂ)
  (hf : HasRDerivAt f u Df) :
  fderivR (H:=H) (W:=ℂ) (fun x => c * f x) u = (mulLeftCLM c).comp Df := by
  simpa [Function.comp, fderivR, HasRDerivAt]
    using (((mulLeftCLM c).hasFDerivAt).comp u hf).fderiv

/-- `D₊` is additive in the function. -/
lemma Dplus_add
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  DplusCLM (H:=H) (W:=ℂ) (fun x => f x + g x) u
    = DplusCLM (H:=H) (W:=ℂ) f u + DplusCLM (H:=H) (W:=ℂ) g u := by
  have hDf : fderivR (H:=H) (W:=ℂ) f u = Df := hf.fderiv
  have hDg : fderivR (H:=H) (W:=ℂ) g u = Dg := hg.fderiv
  simp [DplusCLM, fderivR_add (H:=H) (u:=u) (hf:=hf) (hg:=hg),
        hDf, hDg, sub_eq_add_neg, Aℒ_add, smul_add, add_comm, add_left_comm, add_assoc]

/-- `D₋` is additive in the function. -/
lemma Dminus_add
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  DminusCLM (H:=H) (W:=ℂ) (fun x => f x + g x) u
    = DminusCLM (H:=H) (W:=ℂ) f u + DminusCLM (H:=H) (W:=ℂ) g u := by
  have hDf : fderivR (H:=H) (W:=ℂ) f u = Df := hf.fderiv
  have hDg : fderivR (H:=H) (W:=ℂ) g u = Dg := hg.fderiv
  simp [DminusCLM, fderivR_add (H:=H) (u:=u) (hf:=hf) (hg:=hg),
        hDf, hDg, Aℒ_add, smul_add, add_left_comm, add_assoc]

/-- `D₊` of a fixed complex multiple. -/
lemma Dplus_const_mul
  {f : H → ℂ} {u : H} {Df : H →L[ℝ] ℂ} (c : ℂ)
  (hf : HasRDerivAt f u Df) :
  DplusCLM (H:=H) (W:=ℂ) (fun x => c * f x) u
    = (mulLeftCLM c).comp (DplusCLM (H:=H) (W:=ℂ) f u) := by
  have hDf : fderivR (H:=H) (W:=ℂ) f u = Df := hf.fderiv
  simp [DplusCLM, fderivR_const_mul (H:=H) (u:=u) (c:=c) hf,
        hDf, mulLeftCLM_comp_eq_smul, Aℒ_smul_complex, sub_eq_add_neg, smul_add]

/-- `D₋` of a fixed complex multiple. -/
lemma Dminus_const_mul
  {f : H → ℂ} {u : H} {Df : H →L[ℝ] ℂ} (c : ℂ)
  (hf : HasRDerivAt f u Df) :
  DminusCLM (H:=H) (W:=ℂ) (fun x => c * f x) u
    = (mulLeftCLM c).comp (DminusCLM (H:=H) (W:=ℂ) f u) := by
  have hDf : fderivR (H:=H) (W:=ℂ) f u = Df := hf.fderiv
  simp [DminusCLM, fderivR_const_mul (H:=H) (u:=u) (c:=c) hf,
        hDf, mulLeftCLM_comp_eq_smul, Aℒ_smul_complex, smul_add]

/-! ### Product rule for `D₊`/`D₋` and Gradients -/

/-- Product rule for `D₊` (operator level). -/
lemma Dplus_mul
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  DplusCLM (H:=H) (W:=ℂ) (fun x => f x * g x) u
    = (mulLeftCLM (f u)).comp (DplusCLM (H:=H) (W:=ℂ) g u)
      + (mulLeftCLM (g u)).comp (DplusCLM (H:=H) (W:=ℂ) f u) := by
  have hmul :
    fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u
      = (mulLeftCLM (f u)).comp (fderivR (H:=H) (W:=ℂ) g u)
        + (mulLeftCLM (g u)).comp (fderivR (H:=H) (W:=ℂ) f u) := by
    simpa [fderivR, mulLeftCLM_comp_eq_smul, Pi.mul_def, hf.fderiv, hg.fderiv]
      using (HasFDerivAt.fderiv (HasFDerivAt.mul hf hg))
  simp [DplusCLM, hmul, ContinuousLinearMap.comp_add,
        add_comm, add_left_comm, add_assoc,
        sub_eq_add_neg, smul_add]

/-- Product rule for `D₋` (operator level). -/
lemma Dminus_mul
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  DminusCLM (H:=H) (W:=ℂ) (fun x => f x * g x) u
    = (mulLeftCLM (f u)).comp (DminusCLM (H:=H) (W:=ℂ) g u)
      + (mulLeftCLM (g u)).comp (DminusCLM (H:=H) (W:=ℂ) f u) := by
  have hmul :
    fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u
      = (mulLeftCLM (f u)).comp (fderivR (H:=H) (W:=ℂ) g u)
        + (mulLeftCLM (g u)).comp (fderivR (H:=H) (W:=ℂ) f u) := by
    simpa [fderivR, mulLeftCLM_comp_eq_smul, Pi.mul_def, hf.fderiv, hg.fderiv]
      using (HasFDerivAt.fderiv (HasFDerivAt.mul hf hg))
  simp [DminusCLM, hmul, ContinuousLinearMap.comp_add,
        add_comm, add_left_comm, add_assoc, smul_add]

/-! ### Scalar combinations for gradients -/
variable [CompleteSpace H]

/-- Scalar combination for `∇₊`: \
`∇₊(α f + β g)[u] = conj α • ∇₊ f[u] + conj β • ∇₊ g[u]`. -/
lemma gradPlus_linear_comb
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ} (α β : ℂ)
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  gradPlus (H:=H) (fun x => α * f x + β * g x) u
    = (star α) • gradPlus (H:=H) f u + (star β) • gradPlus (H:=H) g u := by
  -- First, build `HasRDerivAt` for the scaled functions.
  have hfα : HasRDerivAt (fun x => α * f x) u ((mulLeftCLM α).comp Df) := by
    simpa [HasRDerivAt] using (((mulLeftCLM α).hasFDerivAt).comp u hf)
  have hgβ : HasRDerivAt (fun x => β * g x) u ((mulLeftCLM β).comp Dg) := by
    simpa [HasRDerivAt] using (((mulLeftCLM β).hasFDerivAt).comp u hg)
  -- Now use additivity and constant-multiple rules for `D₊`.
  have hD :
    DplusCLM (H:=H) (W:=ℂ) (fun x => α * f x + β * g x) u
      = (mulLeftCLM α).comp (DplusCLM (H:=H) (W:=ℂ) f u)
        + (mulLeftCLM β).comp (DplusCLM (H:=H) (W:=ℂ) g u) := by
    simpa using
      (by
        have := Dplus_add (H:=H) (u:=u) (hf:=hfα) (hg:=hgβ)
        simpa [Dplus_const_mul (H:=H) (u:=u) (c:=α) hf,
               Dplus_const_mul (H:=H) (u:=u) (c:=β) hg,
               ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp] using this)
  -- Compare via inner products against an arbitrary `v` (FIRST slot).
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  have base :
      inner (𝕜 := ℂ) (gradPlus (H:=H) (fun x => α * f x + β * g x) u) v
        = α * inner (𝕜 := ℂ) (gradPlus (H:=H) f u) v
          + β * inner (𝕜 := ℂ) (gradPlus (H:=H) g u) v := by
    simp [inner_gradPlus_eq_Dplus, hD, ContinuousLinearMap.add_apply]
  -- push the scalars inside the FIRST argument
  simpa [inner_add_left, inner_smul_left] using base

/-- Scalar combination for `∇₋`: \
`∇₋(α f + β g)[u] = α • ∇₋ f[u] + β • ∇₋ g[u]`. -/
lemma gradMinus_linear_comb
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ} (α β : ℂ)
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  gradMinus (H:=H) (fun x => α * f x + β * g x) u
    = α • gradMinus (H:=H) f u + β • gradMinus (H:=H) g u := by
  -- Build scaled `HasRDerivAt`
  have hfα : HasRDerivAt (fun x => α * f x) u ((mulLeftCLM α).comp Df) := by
    simpa [HasRDerivAt] using (((mulLeftCLM α).hasFDerivAt).comp u hf)
  have hgβ : HasRDerivAt (fun x => β * g x) u ((mulLeftCLM β).comp Dg) := by
    simpa [HasRDerivAt] using (((mulLeftCLM β).hasFDerivAt).comp u hg)
  -- Operator identity for D₋
  have hD :
    DminusCLM (H:=H) (W:=ℂ) (fun x => α * f x + β * g x) u
      = (mulLeftCLM α).comp (DminusCLM (H:=H) (W:=ℂ) f u)
        + (mulLeftCLM β).comp (DminusCLM (H:=H) (W:=ℂ) g u) := by
    simpa using
      (by
        have := Dminus_add (H:=H) (u:=u) (hf:=hfα) (hg:=hgβ)
        simpa [Dminus_const_mul (H:=H) (u:=u) (c:=α) hf,
               Dminus_const_mul (H:=H) (u:=u) (c:=β) hg,
               ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp] using this)
  -- Compare via the FIRST slot by conjugating a second-slot identity
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  have base :
      inner (𝕜 := ℂ) v (gradMinus (H:=H) (fun x => α * f x + β * g x) u)
        = α * inner (𝕜 := ℂ) v (gradMinus (H:=H) f u)
          + β * inner (𝕜 := ℂ) v (gradMinus (H:=H) g u) := by
    simp [Dminus_eq_inner_gradMinus, hD, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.comp_apply, mulLeftCLM_apply,
          add_comm, add_left_comm, add_assoc]
  -- flip slots and commute scalars to the left
  have base' := congrArg star base
  have base'' :
      inner (𝕜 := ℂ) (gradMinus (H:=H) (fun x => α * f x + β * g x) u) v
        = (star α) * inner (𝕜 := ℂ) (gradMinus (H:=H) f u) v
          + (star β) * inner (𝕜 := ℂ) (gradMinus (H:=H) g u) v := by
    simpa [star_add, star_mul, inner_conj_symm, mul_comm] using base'
  -- push scalars to the FIRST slot
  simpa [inner_add_left, inner_smul_left] using base''

/-! ### Products turned into gradients -/

/-- Product rule for `∇₊`: \
`∇₊(fg)[u] = conj (f[u]) • ∇₊ g[u] + conj (g[u]) • ∇₊ f[u]`. -/
lemma gradPlus_mul
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  gradPlus (H:=H) (fun x => f x * g x) u
    = (star (f u)) • gradPlus (H:=H) g u
      + (star (g u)) • gradPlus (H:=H) f u := by
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  have hD := Dplus_mul (H:=H) (u:=u) (hf:=hf) (hg:=hg)
  simp [inner_gradPlus_eq_Dplus, hD, ContinuousLinearMap.add_apply, inner_smul_left]

/-- Product rule for `∇₋`: \
`∇₋(fg)[u] = f[u] • ∇₋ g[u] + g[u] • ∇₋ f[u]`. -/
lemma gradMinus_mul
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  gradMinus (H:=H) (fun x => f x * g x) u
    = (f u) • gradMinus (H:=H) g u
      + (g u) • gradMinus (H:=H) f u := by
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  -- start from a second-slot identity and flip the slots
  have hD := Dminus_mul (H:=H) (u:=u) (hf:=hf) (hg:=hg)
  have h2 :
      inner (𝕜 := ℂ) v (gradMinus (H:=H) (fun x => f x * g x) u)
        = (f u) * inner (𝕜 := ℂ) v (gradMinus (H:=H) g u)
          + (g u) * inner (𝕜 := ℂ) v (gradMinus (H:=H) f u) := by
    simp [Dminus_eq_inner_gradMinus, hD, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.comp_apply, mulLeftCLM_apply]
  -- take conjugates to get a FIRST-slot identity
  have h1 := congrArg star h2
  simpa [star_add, star_mul, inner_conj_symm, inner_add_left, inner_smul_left, add_comm, add_left_comm, add_assoc]
    using h1

/-! ### Inverse and quotient -/

private lemma conj_ne_zero_of_ne_zero {z : ℂ} (hz : z ≠ 0) : star z ≠ 0 := by
  intro h; exact hz (by simpa using congrArg star h)

/-- `∇₊(1/g)[u] = - ∇₊ g[u] / (conj (g[u]))^2`, assuming `g[u] ≠ 0`. -/
lemma gradPlus_inv
  {g : H → ℂ} {u : H} {Dg : H →L[ℝ] ℂ}
  (hg : HasRDerivAt g u Dg) (hgu : g u ≠ 0) :
  gradPlus (H:=H) (fun x => (g x)⁻¹) u
    = - ((star (g u))^2)⁻¹ • gradPlus (H:=H) g u := by
  -- derivative of inverse via `HasFDerivAt.inv`
  have h_inv :
      HasRDerivAt (fun x => (g x)⁻¹) u ((mulLeftCLM (-( (g u) ^ 2 )⁻¹)).comp Dg) := by
    simpa [HasRDerivAt, fderivR, mulLeftCLM_comp_eq_smul]
      using (hg.inv hgu)
  -- Push constants through `D₊`, then use Riesz.
  have hD :
      DplusCLM (H:=H) (W:=ℂ) (fun x => (g x)⁻¹) u
        = (mulLeftCLM (-( (g u) ^ 2 )⁻¹)).comp (DplusCLM (H:=H) (W:=ℂ) g u) := by
    simpa using Dplus_const_mul (H:=H) (u:=u) (c:= -((g u)^2)⁻¹) h_inv
  -- Compare in the dual against an arbitrary `v`.
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  have hc : star (g u) ≠ 0 := conj_ne_zero_of_ne_zero hgu
  simp [gradPlus, inner_gradPlus_eq_Dplus, hD, ContinuousLinearMap.comp_apply,
        mulLeftCLM_apply, inner_smul_left, pow_two, inv_pow, hc]

/-- `∇₋(1/g)[u] = - ∇₋ g[u] / (g[u])^2`, assuming `g[u] ≠ 0`. -/
lemma gradMinus_inv
  {g : H → ℂ} {u : H} {Dg : H →L[ℝ] ℂ}
  (hg : HasRDerivAt g u Dg) (hgu : g u ≠ 0) :
  gradMinus (H:=H) (fun x => (g x)⁻¹) u
    = - ((g u)^2)⁻¹ • gradMinus (H:=H) g u := by
  have h_inv :
      HasRDerivAt (fun x => (g x)⁻¹) u ((mulLeftCLM (-( (g u) ^ 2 )⁻¹)).comp Dg) := by
    simpa [HasRDerivAt, fderivR, mulLeftCLM_comp_eq_smul]
      using (hg.inv hgu)
  have hD :
      DminusCLM (H:=H) (W:=ℂ) (fun x => (g x)⁻¹) u
        = (mulLeftCLM (-( (g u) ^ 2 )⁻¹)).comp (DminusCLM (H:=H) (W:=ℂ) g u) := by
    simpa using Dminus_const_mul (H:=H) (u:=u) (c:= -((g u)^2)⁻¹) h_inv
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  simp [gradMinus, Dminus_eq_inner_gradMinus, hD,
        ContinuousLinearMap.comp_apply, mulLeftCLM_apply, inner_smul_right,
        pow_two, inv_pow]

/-- Quotient rule for `∇₊` (stated using `•` instead of dividing vectors):
`∇₊(f/g)[u] = ((conj (g[u]))^2)⁻¹ • ( (conj (g[u])) • ∇₊ f[u] - (conj (f[u])) • ∇₊ g[u] )`,
assuming `g[u] ≠ 0`. -/
lemma gradPlus_div
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) (hgu : g u ≠ 0) :
  gradPlus (H:=H) (fun x => f x / g x) u
    = ((star (g u))^2)⁻¹ •
        ( (star (g u)) • gradPlus (H:=H) f u
          - (star (f u)) • gradPlus (H:=H) g u ) := by
  -- inverse piece
  have hInv : HasRDerivAt (fun x => (g x)⁻¹) u ((mulLeftCLM (-( (g u) ^ 2 )⁻¹)).comp Dg) := by
    simpa [HasRDerivAt, fderivR, mulLeftCLM_comp_eq_smul] using (hg.inv hgu)
  -- product rule at the vector level
  have hmul := gradPlus_mul (H:=H) (u:=u) (hf:=hf) (hg:=hInv)
  -- rewrite f/g as f * (1/g)
  have hfg : (fun x => f x / g x) = (fun x => f x * (g x)⁻¹) := by
    funext x; simp [Pi.div_def]
  -- substitute ∇₊(1/g)
  have hinv := gradPlus_inv (H:=H) (u:=u) (hg:=hg) hgu
  -- algebraic reshuffle on vectors
  calc
    gradPlus (H:=H) (fun x => f x / g x) u
        = gradPlus (H:=H) (fun x => f x * (g x)⁻¹) u := by simpa [hfg]
    _   = (star (f u)) • gradPlus (H:=H) (fun x => (g x)⁻¹) u
            + (star ((g u)⁻¹)) • gradPlus (H:=H) f u := by
            simpa using hmul
    _   = (star (f u)) • ( - ((star (g u))^2)⁻¹ • gradPlus (H:=H) g u )
            + ((star (g u))⁻¹) • gradPlus (H:=H) f u := by
            simpa [hinv, map_inv₀]  -- `map_inv₀`: `star ((g u)⁻¹) = (star (g u))⁻¹`
    _   = ((star (g u))^2)⁻¹ •
            ( (star (g u)) • gradPlus (H:=H) f u
              - (star (f u)) • gradPlus (H:=H) g u ) := by
      -- expand both sides and rearrange using `•` algebra
      simp [smul_add, add_comm, add_left_comm, add_assoc,
            smul_sub, sub_eq_add_neg, smul_smul,
            pow_two, inv_pow, mul_comm, mul_left_comm, mul_assoc]

/-- Quotient rule for `∇₋` (stated using `•` instead of dividing vectors):
`∇₋(f/g)[u] = ( (g[u])^2 )⁻¹ • ( (g[u]) • ∇₋ f[u] - (f[u]) • ∇₋ g[u] )`,
assuming `g[u] ≠ 0`. -/
lemma gradMinus_div
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) (hgu : g u ≠ 0) :
  gradMinus (H:=H) (fun x => f x / g x) u
    = ((g u)^2)⁻¹ •
        ( (g u) • gradMinus (H:=H) f u
          - (f u) • gradMinus (H:=H) g u ) := by
  -- inverse piece
  have hInv : HasRDerivAt (fun x => (g x)⁻¹) u ((mulLeftCLM (-( (g u) ^ 2 )⁻¹)).comp Dg) := by
    simpa [HasRDerivAt, fderivR, mulLeftCLM_comp_eq_smul] using (hg.inv hgu)
  -- product rule at the vector level
  have hmul := gradMinus_mul (H:=H) (u:=u) (hf:=hf) (hg:=hInv)
  -- rewrite f/g as f * (1/g)
  have hfg : (fun x => f x / g x) = (fun x => f x * (g x)⁻¹) := by
    funext x; simp [Pi.div_def]
  -- substitute ∇₋(1/g)
  have hinv := gradMinus_inv (H:=H) (u:=u) (hg:=hg) hgu
  -- algebraic reshuffle on vectors
  calc
    gradMinus (H:=H) (fun x => f x / g x) u
        = gradMinus (H:=H) (fun x => f x * (g x)⁻¹) u := by simpa [hfg]
    _   = (f u) • gradMinus (H:=H) (fun x => (g x)⁻¹) u
            + ((g u)⁻¹) • gradMinus (H:=H) f u := by
            simpa using hmul
    _   = (f u) • ( - ((g u)^2)⁻¹ • gradMinus (H:=H) g u )
            + ((g u)⁻¹) • gradMinus (H:=H) f u := by
            simpa [hinv]
    _   = ((g u)^2)⁻¹ •
            ( (g u) • gradMinus (H:=H) f u
              - (f u) • gradMinus (H:=H) g u ) := by
      simp [smul_add, add_comm, add_left_comm, add_assoc,
            smul_sub, sub_eq_add_neg, smul_smul,
            pow_two, inv_pow, mul_comm, mul_left_comm, mul_assoc]

end algebraic_ops

end Wirtinger
