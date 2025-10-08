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
    ((r : ℂ) * I) • v = (r : ℂ) • (I • v) := by simp [smul_smul]
    _ = (r : ℝ) • (I • v) := rfl

/-- Decomposes a `ℂ`-scalar multiplication into its real and imaginary parts. -/
lemma complexSmul_decompose (a : ℂ) (v : V) :
    a • v = (a.re : ℝ) • v + a.im • I • v := by
  calc
    a • v
      = ((a.re : ℂ) + (a.im : ℂ) * I) • v := by rw [Complex.re_add_im a]
    _ = (a.re : ℂ) • v + ((a.im : ℂ) * I) • v := by rw [add_smul]
    _ = (a.re : ℝ) • v + a.im • I • v := by simp

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
def J (V : Type _) [AddCommGroup V] [Module ℂ V] : V →ₗ[ℝ] V where
  toFun := fun v => (I : ℂ) • v
  map_add' := by intro v w; simp [smul_add]
  map_smul' := by
    intro r v
    rw [smul_comm]
    rfl

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
            simp [map_add]
    _   = (a.re : ℝ) • C.C v + a.im • C.C (I • v) := by
            simp [h_smul₁, h_smul₂]
    _   = (a.re : ℝ) • C.C v + a.im • (-(I • C.C v)) := by
            simp [Conjugation.antiJ_apply]
    _   = (a.re : ℝ) • C.C v - a.im • (I • C.C v) := by
            simp [smul_neg, sub_eq_add_neg]
    _   = ((a.re : ℂ) • C.C v) - (((a.im : ℂ) * I) • C.C v) := by
            simp
    _   = ((a.re : ℂ) - (a.im : ℂ) * I) • C.C v := by
            simp [sub_smul]
    _   = (star a) • C.C v := by
            simp [star_eq_re_sub_im, sub_eq_add_neg]

end algebraic_J

/-! ## Wirtinger Operators -/
section wirtinger_ops

/-- Multiplication by `i` as a continuous `ℝ`-linear map. -/
def Jc (V : Type _) [NormedAddCommGroup V] [NormedSpace ℂ V] : V →L[ℝ] V :=
  { toLinearMap := J V
    , cont := (continuous_id : Continuous fun v : V => v).const_smul (I : ℂ) }

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
      , cont := (continuous_conj.comp D.continuous) }
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
  , cont := (continuous_conj.comp (DminusCLM (H:=H) (W:=ℂ) f u).continuous) }

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
    continuous_conj.comp hcomp
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
      change star ((r : ℂ) * z) = (r : ℂ) * star z
      simp [mul_comm] }
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
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  have h1L :
      (InnerProductSpace.toDual ℂ H)
        (gradPlus (H:=H) (fun x => star (f x)) u)
      = DplusCLM_c_linear (H:=H) (fun x => star (f x)) u := by
    convert
      (LinearIsometryEquiv.apply_symm_apply
        (InnerProductSpace.toDual ℂ H)
        (DplusCLM_c_linear (H:=H) (fun x => star (f x)) u)) using 1
  have h1R :
      (InnerProductSpace.toDual ℂ H)
        (gradMinus (H:=H) f u)
      = DminusCLM_star_c_linear (H:=H) f u := by
    convert
      (LinearIsometryEquiv.apply_symm_apply
        (InnerProductSpace.toDual ℂ H)
        (DminusCLM_star_c_linear (H:=H) f u)) using 1
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
  have h1L :
      (InnerProductSpace.toDual ℂ H)
        (gradMinus (H:=H) (fun x => star (f x)) u)
      = DminusCLM_star_c_linear (H:=H) (fun x => star (f x)) u := by
    convert
      (LinearIsometryEquiv.apply_symm_apply
        (InnerProductSpace.toDual ℂ H)
        (DminusCLM_star_c_linear (H:=H) (fun x => star (f x)) u)) using 1
  have h1R :
      (InnerProductSpace.toDual ℂ H)
        (gradPlus (H:=H) f u)
      = DplusCLM_c_linear (H:=H) f u := by
    convert
      (LinearIsometryEquiv.apply_symm_apply
        (InnerProductSpace.toDual ℂ H)
        (DplusCLM_c_linear (H:=H) f u)) using 1
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

/-! ### Helpers for scalar algebra -/

@[simp] lemma star_inv (z : ℂ) : star (z)⁻¹ = (star z)⁻¹ := by
  change (starRingEnd ℂ) (z⁻¹) = ((starRingEnd ℂ) z)⁻¹
  exact (map_inv₀ (starRingEnd ℂ) z)

@[simp] lemma mul_inv_mul_inv (a : ℂ) : a * (a⁻¹ * a⁻¹) = (a : ℂ)⁻¹ := by
  by_cases h : a = 0
  · simp [h]
  · have h1 : a * a⁻¹ = (1 : ℂ) := by simp [h]
    calc
      a * (a⁻¹ * a⁻¹) = (a * a⁻¹) * a⁻¹ := by simp [mul_assoc]
      _ = 1 * a⁻¹ := by simp [h1]
      _ = a⁻¹ := by simp

/-! ### Left-multiplication by a fixed complex number as an ℝ-CLM -/
/-- `ℂ`-left multiplication by a fixed `c` as a continuous `ℝ`-linear map. -/
def mulLeftCLM (c : ℂ) : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := fun z => c * z
  , map_add' := by intro x y; simp [mul_add]
  , map_smul' := by intro r z; simp [Algebra.smul_def, mul_comm, mul_left_comm] }
, cont := by simpa using (continuous_const.mul continuous_id) }

@[simp] lemma mulLeftCLM_apply (c z : ℂ) : mulLeftCLM c z = c * z := rfl

/-- `Aℒ` commutes with fixed complex left multiplication on `ℂ`. -/
@[simp] lemma Aℒ_comp_mulLeftCLM (T : H →L[ℝ] ℂ) (c : ℂ) :
    Aℒ (H:=H) (W:=ℂ) ((mulLeftCLM c).comp T)
  = (mulLeftCLM c).comp (Aℒ (H:=H) (W:=ℂ) T) := by
  ext v; simp [Aℒ, ContinuousLinearMap.comp_apply, Jc_apply, mul_left_comm]

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

@[simp] lemma Aℒ_smul_complex (c : ℂ) (T : H →L[ℝ] ℂ) :
    Aℒ (H:=H) (W:=ℂ) (c • T) = c • Aℒ (H:=H) (W:=ℂ) T := by
  simpa [mulLeftCLM_comp_eq_smul] using
    (Aℒ_comp_mulLeftCLM (H:=H) (T:=T) (c:=c))

@[simp] lemma Aℒ_neg (T : H →L[ℝ] ℂ) :
    Aℒ (H:=H) (W:=ℂ) (-T) = - Aℒ (H:=H) (W:=ℂ) T := by
  ext v; simp [Aℒ]

@[simp] lemma real_smul_comm_complex
    (r : ℝ) (c : ℂ) (T : H →L[ℝ] ℂ) :
    r • (c • T) = c • (r • T) := by
  ext v; simp [Algebra.smul_def, mul_comm, mul_left_comm]

/-! ### Linearity in the function: sums and constant complex multiples -/

lemma fderivR_add
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  fderivR (H:=H) (W:=ℂ) (fun x => f x + g x) u = Df + Dg := by
  simpa [HasRDerivAt, fderivR] using ((hf.add hg).fderiv)

lemma fderivR_const_mul
  {f : H → ℂ} {u : H} {Df : H →L[ℝ] ℂ} (c : ℂ)
  (hf : HasRDerivAt f u Df) :
  fderivR (H:=H) (W:=ℂ) (fun x => c * f x) u = (mulLeftCLM c).comp Df := by
  simpa [Function.comp, fderivR, HasRDerivAt]
    using (((mulLeftCLM c).hasFDerivAt).comp u hf).fderiv

lemma Dplus_add
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  DplusCLM (H:=H) (W:=ℂ) (fun x => f x + g x) u
    = DplusCLM (H:=H) (W:=ℂ) f u + DplusCLM (H:=H) (W:=ℂ) g u := by
  have hDf : fderivR (H:=H) (W:=ℂ) f u = Df := hf.fderiv
  have hDg : fderivR (H:=H) (W:=ℂ) g u = Dg := hg.fderiv
  simp [DplusCLM, fderivR_add (H:=H) (u:=u) (hf:=hf) (hg:=hg),
        hDf, hDg, sub_eq_add_neg, Aℒ_add, smul_add, add_comm, add_left_comm, add_assoc]

lemma Dminus_add
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  DminusCLM (H:=H) (W:=ℂ) (fun x => f x + g x) u
    = DminusCLM (H:=H) (W:=ℂ) f u + DminusCLM (H:=H) (W:=ℂ) g u := by
  have hDf : fderivR (H:=H) (W:=ℂ) f u = Df := hf.fderiv
  have hDg : fderivR (H:=H) (W:=ℂ) g u = Dg := hg.fderiv
  simp [DminusCLM, fderivR_add (H:=H) (u:=u) (hf:=hf) (hg:=hg),
        hDf, hDg, Aℒ_add, smul_add, add_left_comm, add_assoc]

lemma Dplus_const_mul
  {f : H → ℂ} {u : H} {Df : H →L[ℝ] ℂ} (c : ℂ)
  (hf : HasRDerivAt f u Df) :
  DplusCLM (H:=H) (W:=ℂ) (fun x => c * f x) u
    = (mulLeftCLM c).comp (DplusCLM (H:=H) (W:=ℂ) f u) := by
  have hDf : fderivR (H:=H) (W:=ℂ) f u = Df := hf.fderiv
  simp [DplusCLM, fderivR_const_mul (H:=H) (u:=u) (c:=c) hf,
        hDf, mulLeftCLM_comp_eq_smul, Aℒ_smul_complex, sub_eq_add_neg, smul_add]

lemma Dminus_const_mul
  {f : H → ℂ} {u : H} {Df : H →L[ℝ] ℂ} (c : ℂ)
  (hf : HasRDerivAt f u Df) :
  DminusCLM (H:=H) (W:=ℂ) (fun x => c * f x) u
    = (mulLeftCLM c).comp (DminusCLM (H:=H) (W:=ℂ) f u) := by
  have hDf : fderivR (H:=H) (W:=ℂ) f u = Df := hf.fderiv
  simp [DminusCLM, fderivR_const_mul (H:=H) (u:=u) (c:=c) hf,
        hDf, mulLeftCLM_comp_eq_smul, Aℒ_smul_complex, smul_add]

/-! ### Product rule for `D₊`/`D₋` and Gradients -/

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
  simp [DminusCLM, hmul, ContinuousLinearMap.comp_add, smul_add,
        add_comm, add_left_comm, add_assoc]

@[simp] lemma inner_smul_right_comm (x y : H) (a : ℂ) :
    inner (𝕜 := ℂ) x (a • y) = inner (𝕜 := ℂ) x y * a := by
  simp [mul_comm]
@[simp] lemma inner_smul_left_comm (a : ℂ) (x y : H) :
    inner (𝕜 := ℂ) (a • x) y = inner (𝕜 := ℂ) x y * (star a) := by
  simp

/-- Canonical inverse chain rule over `ℝ` (restrictScalars version). -/
lemma hasRDerivAt_inv_from_hasDeriv
  {g : H → ℂ} {u : H} {Dg : H →L[ℝ] ℂ}
  (hg : HasRDerivAt g u Dg)
  {c : ℂ}
  (hc : HasFDerivAt (fun z : ℂ => z⁻¹)
          ((1 : ℂ →L[ℂ] ℂ).smulRight c) (g u)) :
  HasRDerivAt (fun x => (g x)⁻¹) u
    (ContinuousLinearMap.comp
      (ContinuousLinearMap.restrictScalars (R:=ℝ)
        ((1 : ℂ →L[ℂ] ℂ).smulRight c))
      Dg) := by
  exact (hc.restrictScalars ℝ).comp u hg

variable [CompleteSpace H]

/-- Scalar combination for `∇₊`: \
`∇₊(α f + β g)[u] = conj α • ∇₊ f[u] + conj β • ∇₊ g[u]`. -/
lemma gradPlus_linear_comb
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ} (α β : ℂ)
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  gradPlus (H:=H) (fun x => α * f x + β * g x) u
    = (star α) • gradPlus (H:=H) f u + (star β) • gradPlus (H:=H) g u := by
  have hfα : HasRDerivAt (fun x => α * f x) u ((mulLeftCLM α).comp Df) := by
    simpa [HasRDerivAt] using (((mulLeftCLM α).hasFDerivAt).comp u hf)
  have hgβ : HasRDerivAt (fun x => β * g x) u ((mulLeftCLM β).comp Dg) := by
    simpa [HasRDerivAt] using (((mulLeftCLM β).hasFDerivAt).comp u hg)
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
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  have base :
      inner (𝕜 := ℂ) (gradPlus (H:=H) (fun x => α * f x + β * g x) u) v
        = α * inner (𝕜 := ℂ) (gradPlus (H:=H) f u) v
          + β * inner (𝕜 := ℂ) (gradPlus (H:=H) g u) v := by
    simp [inner_gradPlus_eq_Dplus, hD, ContinuousLinearMap.add_apply]
  simpa [inner_add_left, inner_smul_left] using base

/-- Scalar combination for `∇₋`:
`∇₋(α f + β g)[u] = α • ∇₋ f[u] + β • ∇₋ g[u]`. -/
lemma gradMinus_linear_comb
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ} (α β : ℂ)
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  gradMinus (H:=H) (fun x => α * f x + β * g x) u
    = α • gradMinus (H:=H) f u + β • gradMinus (H:=H) g u := by
  -- build derivative facts for α f and β g
  have hfα : HasRDerivAt (fun x => α * f x) u ((mulLeftCLM α).comp Df) := by
    simpa [HasRDerivAt] using (((mulLeftCLM α).hasFDerivAt).comp u hf)
  have hgβ : HasRDerivAt (fun x => β * g x) u ((mulLeftCLM β).comp Dg) := by
    simpa [HasRDerivAt] using (((mulLeftCLM β).hasFDerivAt).comp u hg)
  -- operator-level identity for D₋
  have hD :
    DminusCLM (H:=H) (W:=ℂ) (fun x => α * f x + β * g x) u
      = (mulLeftCLM α).comp (DminusCLM (H:=H) (W:=ℂ) f u)
        + (mulLeftCLM β).comp (DminusCLM (H:=H) (W:=ℂ) g u) := by
    simpa using
      (by
        have := Dminus_add (H:=H) (u:=u) (hf:=hfα) (hg:=hgβ)
        simpa [ Dminus_const_mul (H:=H) (u:=u) (c:=α) hf
              , Dminus_const_mul (H:=H) (u:=u) (c:=β) hg
              , ContinuousLinearMap.comp_add
              , ContinuousLinearMap.add_comp] using this)
  -- use Riesz injectivity
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  -- (1) apply the operator identity pointwise at v
  have hD_v :
      DminusCLM (H:=H) (W:=ℂ) (fun x => α * f x + β * g x) u v
        = α * DminusCLM (H:=H) (W:=ℂ) f u v
          + β * DminusCLM (H:=H) (W:=ℂ) g u v := by
    simpa [ ContinuousLinearMap.add_apply
          , ContinuousLinearMap.comp_apply
          , mulLeftCLM_apply ]
      using congrArg (fun T : H →L[ℝ] ℂ => T v) hD
  -- (2) convert every `D₋ … v` to the inner-product form with v on the left
  have base :
      inner (𝕜 := ℂ) v (gradMinus (H:=H) (fun x => α * f x + β * g x) u)
        = α * inner (𝕜 := ℂ) v (gradMinus (H:=H) f u)
          + β * inner (𝕜 := ℂ) v (gradMinus (H:=H) g u) := by
    simpa [ Dminus_eq_inner_gradMinus
              (f := fun x => α * f x + β * g x) (u := u) (v := v)
          , Dminus_eq_inner_gradMinus (f := f) (u := u) (v := v)
          , Dminus_eq_inner_gradMinus (f := g) (u := u) (v := v) ] using hD_v
  -- (3) take `star` to move to the first slot, then finish with `inner` linearity
  have base' := congrArg star base
  have base'' :
      inner (𝕜 := ℂ) (gradMinus (H:=H) (fun x => α * f x + β * g x) u) v
        = (star α) * inner (𝕜 := ℂ) (gradMinus (H:=H) f u) v
          + (star β) * inner (𝕜 := ℂ) (gradMinus (H:=H) g u) v := by
    simpa [star_add, star_mul, inner_conj_symm, mul_comm] using base'
  simpa [inner_add_left, inner_smul_left] using base''

/-! ### Products turned into gradients -/

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

lemma gradMinus_mul
  {f g : H → ℂ} {u : H} {Df Dg : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u Df) (hg : HasRDerivAt g u Dg) :
  gradMinus (H:=H) (fun x => f x * g x) u
    = (f u) • gradMinus (H:=H) g u
      + (g u) • gradMinus (H:=H) f u := by
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  -- Operator-level product rule
  have hD := Dminus_mul (H:=H) (u:=u) (hf:=hf) (hg:=hg)
  -- Specialize at v to turn CLM identities into scalar equalities
  have hD_v :
      DminusCLM (H:=H) (W:=ℂ) (fun x => f x * g x) u v
        = (f u) * DminusCLM (H:=H) (W:=ℂ) g u v
          + (g u) * DminusCLM (H:=H) (W:=ℂ) f u v := by
    simpa [ ContinuousLinearMap.add_apply
          , ContinuousLinearMap.comp_apply
          , mulLeftCLM_apply ]
      using congrArg (fun T : H →L[ℝ] ℂ => T v) hD
  -- Convert every D₋ … v to inner form with v on the left
  have base :
      inner (𝕜 := ℂ) v (gradMinus (H:=H) (fun x => f x * g x) u)
        = (f u) * inner (𝕜 := ℂ) v (gradMinus (H:=H) g u)
          + (g u) * inner (𝕜 := ℂ) v (gradMinus (H:=H) f u) := by
    simpa [ Dminus_eq_inner_gradMinus
              (f := fun x => f x * g x) (u := u) (v := v)
          , Dminus_eq_inner_gradMinus (f := g) (u := u) (v := v)
          , Dminus_eq_inner_gradMinus (f := f) (u := u) (v := v) ] using hD_v
  -- Move to the first slot by taking star, then finish with linearity in the first slot
  have base' := congrArg star base
  have base'' :
      inner (𝕜 := ℂ) (gradMinus (H:=H) (fun x => f x * g x) u) v
        = (star (f u)) * inner (𝕜 := ℂ) (gradMinus (H:=H) g u) v
          + (star (g u)) * inner (𝕜 := ℂ) (gradMinus (H:=H) f u) v := by
    simpa [star_add, star_mul, inner_conj_symm, mul_comm] using base'
  -- Reassemble RHS as ⟪(f u)•∇₋g + (g u)•∇₋f, v⟫
  simpa [inner_add_left, inner_smul_left] using base''

/-! ### Inverse and quotient -/

/-- `(((1 : ℂ →L[ℂ] ℂ).smulRight c)`, viewed over `ℝ`, is just left-multiplication by `c`. -/
@[simp] lemma smulRight_id_restrict_eq_mulLeft (c : ℂ) :
    (ContinuousLinearMap.restrictScalars (R:=ℝ) ((1 : ℂ →L[ℂ] ℂ).smulRight c))
      = mulLeftCLM c := by
  ext z; simp [mul_comm]

/-- Helper: rewrite the scalar appearing in the derivative of `z ↦ z⁻¹`. -/
@[simp] lemma inv_sq_eq_inv_mul_inv (w : ℂ) : (w^2)⁻¹ = w⁻¹ * w⁻¹ := by
  simp [pow_two]

/-- Over `ℂ`, the Fréchet derivative of `z ↦ z⁻¹` at a nonzero `w` is
`((1 : ℂ →L[ℂ] ℂ).smulRight (-(w⁻¹ * w⁻¹)))`. -/
lemma hasFDerivAt_inv_smulRight (w : ℂ) (hw : w ≠ 0) :
  HasFDerivAt (fun z : ℂ => z⁻¹)
    ((1 : ℂ →L[ℂ] ℂ).smulRight (-(w⁻¹ * w⁻¹))) w := by
  simpa [inv_sq_eq_inv_mul_inv] using
    (hasDerivAt_inv (𝕜 := ℂ) hw).hasFDerivAt

/-- `∇₋(1/g)[u] = - (g[u]⁻¹ * g[u]⁻¹) • ∇₋ g[u]`, assuming `g[u] ≠ 0`. -/
lemma gradMinus_inv
  {g : H → ℂ} {u : H} {Dg : H →L[ℝ] ℂ}
  (hg : HasRDerivAt g u Dg) (hgu : g u ≠ 0) :
  gradMinus (H:=H) (fun x => (g x)⁻¹) u
    = - ((g u)⁻¹ * (g u)⁻¹) • gradMinus (H:=H) g u := by
  classical
  -- convenient name for the scalar
  set c : ℂ := -((g u)⁻¹ * (g u)⁻¹)
  -- analytic chain rule (over ℂ), then restrict
  have hc :
      HasFDerivAt (fun z : ℂ => z⁻¹)
        ((1 : ℂ →L[ℂ] ℂ).smulRight c) (g u) := by
    simpa [c] using hasFDerivAt_inv_smulRight (w := g u) hgu
  have hInvR :
      HasRDerivAt (fun x => (g x)⁻¹) u
        ((mulLeftCLM c).comp Dg) := by
    have := hasRDerivAt_inv_from_hasDeriv (H:=H) (g:=g) (u:=u) (Dg:=Dg) hg hc
    simpa [smulRight_id_restrict_eq_mulLeft] using this
  -- operator identity for D₋ at u, in one `simp` step (no algebraic subgoals)
  have hD :
      DminusCLM (H:=H) (W:=ℂ) (fun x => (g x)⁻¹) u
        = (mulLeftCLM c).comp (DminusCLM (H:=H) (W:=ℂ) g u) := by
    simp [DminusCLM, hInvR.fderiv, hg.fderiv, ContinuousLinearMap.comp_add,
          mulLeftCLM_comp_eq_smul, smul_add, real_smul_comm_complex, c]
  -- specialize at v and convert to inner-product form with v on the left (fits ∇₋)
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  have hD_v :
      DminusCLM (H:=H) (W:=ℂ) (fun x => (g x)⁻¹) u v
        = c * DminusCLM (H:=H) (W:=ℂ) g u v := by
    simpa [ContinuousLinearMap.comp_apply, mulLeftCLM_apply] using
      congrArg (fun T : H →L[ℝ] ℂ => T v) hD
  have hv :
      inner (𝕜 := ℂ) v (gradMinus (H:=H) (fun x => (g x)⁻¹) u)
        = c * inner (𝕜 := ℂ) v (gradMinus (H:=H) g u) := by
    simpa [ Dminus_eq_inner_gradMinus
          , (Dminus_eq_inner_gradMinus (f:=g) (u:=u) (v:=v)) ] using hD_v
  -- flip to the first slot via `star`, then repackage the scalar with `inner_smul_left`
  -- so that the vector scalar is exactly `c` (not `star c`)
  have hv' := congrArg star hv
  -- LHS: star ⟪v, x⟫ = ⟪x, v⟫; RHS: star (c * t) = star t * star c
  -- `inner_smul_left`: ⟪c • y, v⟫ = ⟪y, v⟫ * star c
  simpa [ inner_conj_symm, star_mul, inner_smul_left
        , mul_comm, mul_left_comm, mul_assoc
        , c ] using hv'

/-- `∇₊(1/g)[u] = - ((conj g[u])⁻¹ * (conj g[u])⁻¹) • ∇₊ g[u]`, assuming `g[u] ≠ 0`. -/
lemma gradPlus_inv
  {g : H → ℂ} {u : H} {Dg : H →L[ℝ] ℂ}
  (hg : HasRDerivAt g u Dg) (hgu : g u ≠ 0) :
  gradPlus (H:=H) (fun x => (g x)⁻¹) u
    = - ((star (g u))⁻¹ * (star (g u))⁻¹) • gradPlus (H:=H) g u := by
  classical
  set c : ℂ := -((g u)⁻¹ * (g u)⁻¹)
  -- same analytic chain rule as above
  have hc :
      HasFDerivAt (fun z : ℂ => z⁻¹)
        ((1 : ℂ →L[ℂ] ℂ).smulRight c) (g u) := by
    simpa [c] using hasFDerivAt_inv_smulRight (w := g u) hgu
  have hInvR :
      HasRDerivAt (fun x => (g x)⁻¹) u
        ((mulLeftCLM c).comp Dg) := by
    have := hasRDerivAt_inv_from_hasDeriv (H:=H) (g:=g) (u:=u) (Dg:=Dg) hg hc
    simpa [smulRight_id_restrict_eq_mulLeft] using this
  -- operator identity for D₊ at u (one shot)
  have hD :
      DplusCLM (H:=H) (W:=ℂ) (fun x => (g x)⁻¹) u
        = (mulLeftCLM c).comp (DplusCLM (H:=H) (W:=ℂ) g u) := by
    simp [DplusCLM, hInvR.fderiv, hg.fderiv, mulLeftCLM_comp_eq_smul,
          sub_eq_add_neg, smul_add, real_smul_comm_complex, c]
  -- Riesz in the first slot: this directly introduces `star c`
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v
  have hD_v :
      DplusCLM (H:=H) (W:=ℂ) (fun x => (g x)⁻¹) u v
        = c * DplusCLM (H:=H) (W:=ℂ) g u v := by
    simpa [ContinuousLinearMap.comp_apply, mulLeftCLM_apply] using
      congrArg (fun T : H →L[ℝ] ℂ => T v) hD
  have hv :
      inner (𝕜 := ℂ) (gradPlus (H:=H) (fun x => (g x)⁻¹) u) v
        = c * inner (𝕜 := ℂ) (gradPlus (H:=H) g u) v := by
    simpa [inner_gradPlus_eq_Dplus] using hD_v
  -- `inner_smul_left`: ⟪(star c) • y, v⟫ = (star c) * ⟪y, v⟫
  -- so rewrite the RHS as the inner of a scaled vector
  simpa [ inner_smul_left
        , star_mul, star_inv, map_neg
        , mul_comm, mul_left_comm, mul_assoc
        , c ] using hv

/-! ### Convenience inner-product forms for the inverse rules -/
section inverse_inner_forms
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[simp] lemma inner_gradMinus_inv_left
  {g : H → ℂ} {u : H} {Dg : H →L[ℝ] ℂ}
  (hg : HasRDerivAt g u Dg) (hgu : g u ≠ 0) (v : H) :
  inner (𝕜 := ℂ) (gradMinus (H:=H) (fun x => (g x)⁻¹) u) v
    = -(((star (g u))⁻¹) * ((star (g u))⁻¹)) * inner (𝕜 := ℂ) (gradMinus (H:=H) g u) v := by
  have h :=
    congrArg (fun z => inner (𝕜 := ℂ) z v)
      (gradMinus_inv (H:=H) (u:=u) (g:=g) (Dg:=Dg) hg hgu)
  simpa [ inner_smul_left
        , star_mul, star_inv, map_neg
        , mul_comm, mul_left_comm, mul_assoc ] using h

@[simp] lemma inner_gradPlus_inv_left
  {g : H → ℂ} {u : H} {Dg : H →L[ℝ] ℂ}
  (hg : HasRDerivAt g u Dg) (hgu : g u ≠ 0) (v : H) :
  inner (𝕜 := ℂ) (gradPlus (H:=H) (fun x => (g x)⁻¹) u) v
    = -((g u)⁻¹ * (g u)⁻¹) * inner (𝕜 := ℂ) (gradPlus (H:=H) g u) v := by
  have h :=
    congrArg (fun z => inner (𝕜 := ℂ) z v)
      (gradPlus_inv (H:=H) (u:=u) (g:=g) (Dg:=Dg) hg hgu)
  simpa [ inner_smul_left
        , mul_comm, mul_left_comm, mul_assoc
        , star_mul, star_inv, map_neg ] using h

end inverse_inner_forms

end algebraic_ops

/-! ## Real Gradient (scalar real-valued) -/
section real_gradient
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A scalar function is *real-valued* if `star (f x) = f x` for all `x`. -/
def IsRealValued (f : H → ℂ) : Prop := ∀ x, star (f x) = f x

/-- For a real-valued `f`, the derivative output is real: `star (Df[u] v) = Df[u] v`. -/
lemma fderivR_output_real
  {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) (hreal : IsRealValued f) (v : H) :
  star (fderivR (H:=H) (W:=ℂ) f u v) = fderivR (H:=H) (W:=ℂ) f u v := by
  -- `f̄ = f` as functions (normalize to `starRingEnd` form so rewriting hits `fderivR`)
  have hfunR : (fun x => (starRingEnd ℂ) (f x)) = f := by
    funext x; simpa using hreal x
  -- derivative of conjugate is `conjCLM ∘ D`
  have h := fderivR_conj_of_hasDeriv (H:=H) (f:=f) (u:=u) (D:=D) hf
  -- rewrite the function to `f`, then compare with `hf.fderiv`
  have h2 : conjCLM.comp D = fderivR (H:=H) (W:=ℂ) f u := by
    have := h.symm
    simpa [hfunR] using this
  -- apply both sides at `v`
  have := congrArg (fun T : H →L[ℝ] ℂ => T v) h2
  simpa [conjCLM_apply, hf.fderiv] using this

variable [CompleteSpace H]

/-- For a real-valued `f`, we have `∇₊ f[u] = ∇₋ f[u]`. -/
lemma gradPlus_eq_gradMinus_of_realValued
  {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) (hreal : IsRealValued f) :
  gradPlus (H:=H) f u = gradMinus (H:=H) f u := by
  -- identify `f̄` with `f`
  let g := fun x => star (f x)
  have hfun : g = f := funext hreal
  -- from earlier: ∇₊(f̄) = ∇₋ f
  have h₁ : gradPlus (H:=H) g u = gradMinus (H:=H) f u :=
    gradPlus_conj_eq_gradMinus (H:=H) (f:=f) (u:=u) (D:=D) hf
  -- but `g = f`, hence `∇₊ g[u] = ∇₊ f[u]`
  have h₂ : gradPlus (H:=H) g u = gradPlus (H:=H) f u := by
    -- use Riesz: equality of `D₊` implies equality of `∇₊`
    apply (InnerProductSpace.toDual ℂ H).injective
    ext v
    simp [inner_gradPlus_eq_Dplus, hfun, g]
  -- chain equalities
  have h₂' : gradPlus (H:=H) f u = gradPlus (H:=H) g u := h₂.symm
  simpa [g] using h₂'.trans h₁

/-- A handy algebraic fact: `z + star z = (2 : ℝ) • (z.re : ℂ)`. -/
@[simp] lemma add_star_eq_two_smul_re (z : ℂ) :
  z + star z = (2 : ℝ) • ((z.re : ℂ)) := by
  -- Prove by comparing real and imaginary parts
  apply Complex.ext <;> simp [two_smul]

/-- Define the *real gradient* as the common value `∇₊ f[u] = ∇₋ f[u]` when `f` is real-valued. -/
def gradReal (f : H → ℂ) (u : H) : H := gradPlus (H:=H) f u

@[simp] lemma gradReal_eq_gradPlus (f : H → ℂ) (u : H) :
  gradReal (H:=H) f u = gradPlus (H:=H) f u := rfl

/-- For a real-valued `f`, `∇ℝ f[u] = ∇₋ f[u]`. -/
lemma gradReal_eq_gradMinus
  {f : H → ℂ} {u : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) (hreal : IsRealValued f) :
  gradReal (H:=H) f u = gradMinus (H:=H) f u := by
  simpa [gradReal] using (gradPlus_eq_gradMinus_of_realValued (H:=H) (u:=u) (D:=D) hf hreal)

/-- **Real gradient identities** (packaged as four equalities). -/
lemma real_gradient_formulas
  {f : H → ℂ} {u v : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) (hreal : IsRealValued f) :
  fderivR (H:=H) (W:=ℂ) f u v
    = inner (𝕜 := ℂ) (gradPlus (H:=H) f u) v
      + inner (𝕜 := ℂ) v (gradMinus (H:=H) f u)
    ∧ fderivR (H:=H) (W:=ℂ) f u v
    = inner (𝕜 := ℂ) v (gradPlus (H:=H) f u)
      + inner (𝕜 := ℂ) (gradMinus (H:=H) f u) v
    ∧ fderivR (H:=H) (W:=ℂ) f u v
    = inner (𝕜 := ℂ) (gradReal (H:=H) f u) v
      + inner (𝕜 := ℂ) v (gradReal (H:=H) f u)
    ∧ fderivR (H:=H) (W:=ℂ) f u v
    = (2 : ℝ) • (((inner (𝕜 := ℂ) (gradReal (H:=H) f u) v).re : ℂ)) := by
  -- base split
  have hsplit := fderivR_apply_split_grad (H:=H) (f:=f) (u:=u) (v:=v)
  -- output is real: (Df v) = star (Df v)
  have hrealD :
      fderivR (H:=H) (W:=ℂ) f u v
        = star (fderivR (H:=H) (W:=ℂ) f u v) := by
    simpa using (fderivR_output_real (H:=H) (f:=f) (u:=u) (D:=D) hf hreal v).symm
  -- symmetric split by conjugating and using `hrealD`
  have hsymm :
      fderivR (H:=H) (W:=ℂ) f u v
        = inner (𝕜 := ℂ) v (gradPlus (H:=H) f u)
          + inner (𝕜 := ℂ) (gradMinus (H:=H) f u) v := by
    have hconj := congrArg star hsplit
    have hL : star (fderivR (H:=H) (W:=ℂ) f u v)
              = fderivR (H:=H) (W:=ℂ) f u v := hrealD.symm
    simpa [hL, star_add, inner_conj_symm] using hconj
  -- compress to the real gradient (`∇₊ = ∇₋`)
  have hgm : gradReal (H:=H) f u = gradMinus (H:=H) f u :=
    gradReal_eq_gradMinus (H:=H) (f:=f) (u:=u) (D:=D) hf hreal
  have hpm :
      gradPlus (H:=H) f u = gradMinus (H:=H) f u :=
    gradPlus_eq_gradMinus_of_realValued (H:=H) (f:=f) (u:=u) (D:=D) hf hreal
  -- the 2Re formula for the *sum of the two inners* written with ∇ℝ
  have h2Re :
      inner (𝕜 := ℂ) (gradReal (H:=H) f u) v
        + inner (𝕜 := ℂ) v (gradReal (H:=H) f u)
        = (2 : ℝ) • (((inner (𝕜 := ℂ) (gradReal (H:=H) f u) v).re : ℂ)) := by
    simpa [inner_conj_symm] using
      add_star_eq_two_smul_re (inner (𝕜 := ℂ) (gradReal (H:=H) f u) v)
  refine ⟨hsplit, hsymm, ?hRG, ?h2Re_final⟩
  · -- `Df = ⟪∇ℝ, v⟫ + ⟪v, ∇ℝ⟫`
    -- rewrite *both* ∇₊ and ∇₋ to ∇ℝ using `hpm` and `hgm`
    simpa [gradReal, hgm, hpm] using hsplit
  · -- use the previous conjunct and the 2Re identity
    have hRG :
      fderivR (H:=H) (W:=ℂ) f u v
        = inner (𝕜 := ℂ) (gradReal (H:=H) f u) v
          + inner (𝕜 := ℂ) v (gradReal (H:=H) f u) := by
      simpa [gradReal, hgm, hpm] using hsplit
    simpa [hRG] using h2Re

/-- A concise corollary of the previous lemma:
If `f` is real-valued, then for all `v`,
`Df[u][v] = ⟪∇ℝ f[u], v⟫ + ⟪v, ∇ℝ f[u]⟫ = (2 : ℝ) • Re ⟪∇ℝ f[u], v⟫`. -/
lemma fderivR_real_gradient
  {f : H → ℂ} {u v : H} {D : H →L[ℝ] ℂ}
  (hf : HasRDerivAt f u D) (hreal : IsRealValued f) :
  fderivR (H:=H) (W:=ℂ) f u v
    = inner (𝕜 := ℂ) (gradReal (H:=H) f u) v
      + inner (𝕜 := ℂ) v (gradReal (H:=H) f u)
    ∧ fderivR (H:=H) (W:=ℂ) f u v
    = (2 : ℝ) • (((inner (𝕜 := ℂ) (gradReal (H:=H) f u) v).re : ℂ)) := by
  obtain ⟨_, _, hRG, h2Re⟩ :=
    real_gradient_formulas (H:=H) (f:=f) (u:=u) (v:=v) (D:=D) hf hreal
  exact ⟨hRG, h2Re⟩

end real_gradient

/-! ## Complex Gradient -/
section complex_gradient
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Holomorphic at `u`: the `ℂ`-antilinear Wirtinger gradient vanishes. -/
def IsHolomorphicAt (f : H → ℂ) (u : H) : Prop :=
  gradMinus (H := H) f u = 0

/-- Equivalence between holomorphicity and the vanishing of `D₋`. -/
lemma isHolomorphicAt_iff_DminusCLM_zero (f : H → ℂ) (u : H) :
  IsHolomorphicAt (H := H) f u
    ↔ DminusCLM (H := H) (W := ℂ) f u = 0 := by
  constructor
  · intro h
    -- `∇₋ = 0 ⟹ D₋ = 0` by the Riesz identity for `D₋`
    have h0 : gradMinus (H := H) f u = 0 := h
    ext v
    simp [Dminus_eq_inner_gradMinus, h0]
  · intro hD
    -- `D₋ = 0 ⟹ ∇₋ = 0` by Riesz injectivity
    apply (InnerProductSpace.toDual ℂ H).injective
    ext v
    -- ⟪∇₋, v⟫ = star (D₋ v) = 0
    have hdual :
        inner (𝕜 := ℂ) (gradMinus (H := H) f u) v
          = star (DminusCLM (H := H) (W := ℂ) f u v) := by
      have := congrArg star
        (Dminus_eq_inner_gradMinus (H := H) (f := f) (u := u) (v := v))
      simp
    have hDv : DminusCLM (H := H) (W := ℂ) f u v = 0 := by
      have := congrArg (fun T : H →L[ℝ] ℂ => T v) hD
      simpa using this
    simp [hdual, hDv]

/-- The complex gradient is, by definition, the `∇₊` Wirtinger gradient. -/
def gradC (f : H → ℂ) (u : H) : H := gradPlus (H := H) f u
@[simp] lemma gradC_eq_gradPlus (f : H → ℂ) (u : H) :
  gradC (H := H) f u = gradPlus (H := H) f u := rfl

/-- If `f` is holomorphic at `u`, then `Df[u]` is `ℂ`-linear (as an `ℝ`-CLM). -/
lemma fderivR_isCLinear_of_holomorphic
  {f : H → ℂ} {u : H} (holo : IsHolomorphicAt (H := H) f u) :
  (Jc ℂ).comp (fderivR (H := H) (W := ℂ) f u)
    = (fderivR (H := H) (W := ℂ) f u).comp (Jc H) := by
  -- From `holomorphic` we get `D₋ = 0`, hence `Df = D₊`.
  have hDminus0 : DminusCLM (H := H) (W := ℂ) f u = 0 :=
    (isHolomorphicAt_iff_DminusCLM_zero (H := H) f u).1 holo
  have hDf_eq_Dplus :
      fderivR (H := H) (W := ℂ) f u = DplusCLM (H := H) (W := ℂ) f u := by
    have := (Dplus_add_Dminus (H := H) (W := ℂ) f u).symm
    simpa [hDminus0, add_zero] using this
  -- `D₊` commutes with `J`, hence so does `Df`.
  simpa [hDf_eq_Dplus] using
    (isCLinearR_Dplus (H := H) (W := ℂ) f u)

/-- If `f` is holomorphic at `u`, then the full derivative has the single-slot form
`Df[u][v] = ⟪∇_ℂ f[u], v⟫`. -/
lemma fderivR_apply_holomorphic
  {f : H → ℂ} {u : H} (holo : IsHolomorphicAt (H := H) f u) :
  ∀ v : H,
    fderivR (H := H) (W := ℂ) f u v
      = inner (𝕜 := ℂ) (gradC (H := H) f u) v := by
  intro v
  have hs := fderivR_apply_split_grad (H := H) (f := f) (u := u) (v := v)
  have h0 : gradMinus (H := H) f u = 0 := holo
  simpa [gradC, h0] using hs

/-- For holomorphic `f` we have the identity `∇_ℂ f[u] = ∇₊ f[u]`. -/
@[simp] lemma complexGrad_expr (f : H → ℂ) (u : H) :
  gradC (H := H) f u = gradPlus (H := H) f u := rfl

end complex_gradient

end Wirtinger
