import Mathlib

/-!
# Wirtinger Calculus Formalization

This script formalizes the core concepts of Wirtinger calculus for functions
between complex Hilbert spaces.

## Main Components:
1.  **Real Fréchet Derivative**: Defines derivatives over `ℝ`.
2.  **Complex Structures**: Formalizes the multiplication-by-`i` operator `J` and
    conjugations `C`.
3.  **Wirtinger Operators**: Defines `D₊` and `D₋` and proves their key
    properties (linearity, Wirtinger split).
4.  **Wirtinger Gradients**: For scalar-valued functions, defines `∇₊` and `∇₋`
    using the Riesz representation theorem.
5.  **Adjoint Operators**: Defines and proves identities for `ℂ`-linear and
    `ℂ`-antilinear adjoints.
-/

noncomputable section
open Complex
open ComplexConjugate

namespace Wirtinger

/-! ## Scalar Multiplication Helpers -/
section smul_helpers
variable {V : Type _} [AddCommGroup V] [Module ℂ V]

@[simp] lemma ofReal_smul' (r : ℝ) (v : V) :
    ((r : ℂ) : ℂ) • v = (r : ℝ) • v := rfl

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

/-- A function `f` has a real Fréchet derivative `D` at `u`. -/
abbrev HasRDerivAt (f : H → W) (u : H) (D : H →L[ℝ] W) : Prop := HasFDerivAt f D u

/-- The real Fréchet derivative of `f` at `u`, as a continuous `ℝ`-linear map. -/
@[simp] abbrev fderivR (f : H → W) (u : H) : H →L[ℝ] W := fderiv ℝ f u

/-- The `ℝ`-linear map `t ↦ t • v` as a continuous linear map. -/
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

/-- The Gâteaux derivative equals the Fréchet derivative applied to the direction. -/
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

/-- An `ℝ`-linear conjugation `C` that is involutive and anticommutes with `J`. -/
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

/-- Complex conjugate in terms of real and imaginary parts. -/
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

/-- A `Conjugation` map `C` is conjugate-linear over `ℂ`. -/
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

/-- The continuous `ℝ`-linear map representing multiplication by `i`. -/
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

/-- The anti-twist operator `Aℒ(T) = J ∘ T ∘ J`. -/
@[simp] def Aℒ (T : H →L[ℝ] W) : H →L[ℝ] W := (Jc_W).comp (T.comp Jc_H)

@[simp] lemma Aℒ_apply (T : H →L[ℝ] W) (v : H) :
    Aℒ (H:=H) (W:=W) T v = (I : ℂ) • T ((I : ℂ) • v) := by
  simp [Aℒ, ContinuousLinearMap.comp_apply, Jc_apply]

/-- `Aℒ` is an involution. -/
lemma Aℒ_involutive (T : H →L[ℝ] W) :
    Aℒ (H:=H) (W:=W) (Aℒ T) = T := by
  ext v; simp [Aℒ, ContinuousLinearMap.comp_apply, Jc_apply, smul_smul, Complex.I_mul_I]

/-- Mark Aℒ_involutive as a simp lemma for rewriting. -/
@[simp] lemma Aℒ_Aℒ (T : H →L[ℝ] W) :
  Aℒ (H:=H) (W:=W) (Aℒ T) = T := Aℒ_involutive (H:=H) (W:=W) T

/-- `D₊ f[u]` is the `ℂ`-linear part of the real derivative `Df[u]`. -/
def DplusCLM (f : H → W) (u : H) : H →L[ℝ] W :=
  ((1/2 : ℝ)) • (fderivR f u - Aℒ (H:=H) (W:=W) (fderivR f u))

/-- `D₋ f[u]` is the `ℂ`-antilinear part of the real derivative `Df[u]`. -/
def DminusCLM (f : H → W) (u : H) : H →L[ℝ] W :=
  ((1/2 : ℝ)) • (fderivR f u + Aℒ (H:=H) (W:=W) (fderivR f u))

/-- The Wirtinger operators sum to the real derivative: `D₊ + D₋ = Df`. -/
lemma Dplus_add_Dminus (f : H → W) (u : H) :
    DplusCLM (H:=H) (W:=W) f u + DminusCLM f u = fderivR f u := by
  ext v
  simp only [DplusCLM, DminusCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  rw [← smul_add, sub_add_add_cancel, ← two_smul ℝ]; rw [smul_smul]; norm_num

/-- `D₊` commutes with `J`, corresponding to `ℂ`-linearity in its direction argument. -/
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

/-- `D₋` anticommutes with `J`, corresponding to `ℂ`-antilinearity. -/
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

/-- Pointwise Wirtinger split: `Df[u] v = D₊ f[u] v + D₋ f[u] v`. -/
lemma fderivR_apply_split (f : H → W) (u v : H) :
    fderivR f u v = DplusCLM f u v + DminusCLM f u v := by
  have h := congrArg (fun (T : H →L[ℝ] W) => T v) (Dplus_add_Dminus (H:=H) (W:=W) f u)
  exact h.symm
end wirtinger_ops

/-! ## Scalar-Valued Functions: `ℂ`-Linear Maps -/
section scalar_linear

/-- For a scalar-valued function, `D₊ f[u]` as a continuous `ℂ`-linear map. -/
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

/-- The map `v ↦ star (D₋ f[u] v)` is `ℂ`-linear. Key to defining `∇₋`. -/
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

/-- The `∇₊` gradient, defined via the Riesz representation of `D₊`. -/
def gradPlus (f : H → ℂ) (u : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (DplusCLM_c_linear f u)

/-- The inner product with `∇₊` recovers `D₊`. -/
@[simp] lemma inner_gradPlus_eq_Dplus (f : H → ℂ) (u v : H) :
    inner (𝕜 := ℂ) (gradPlus f u) v
      = DplusCLM (H:=H) (W:=ℂ) f u v := by
  change ((InnerProductSpace.toDual ℂ H) (gradPlus f u)) v
          = DplusCLM (H:=H) (W:=ℂ) f u v
  simp [gradPlus]

/-- The `∇₋` gradient, defined via the Riesz representation of `v ↦ star (D₋ v)`. -/
def gradMinus (f : H → ℂ) (u : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (DminusCLM_star_c_linear f u)

/-- The inner product with `∇₋` (in the second argument) recovers `D₋`. -/
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

/-- Wirtinger split for scalar functions in terms of gradients. -/
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

/-- Wrapper for the standard Hermitian adjoint identity: `⟪x, A y⟫ = ⟪A† x, y⟫`. -/
@[simp] lemma inner_adjoint_linear (A : H →L[ℂ] W) (x : W) (y : H) :
    inner (𝕜 := ℂ) x (A y) = inner (𝕜 := ℂ) ((ContinuousLinearMap.adjoint A) x) y := by
  exact (ContinuousLinearMap.adjoint_inner_left (A := A) (x := y) (y := x)).symm

/- A `section` is used here to group definitions related to the conjugate-linear adjoint.
It shares common variables and assumptions for all definitions inside it.-/
section ConjAdj
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A private helper functional used to define the antilinear adjoint. -/
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

/-- The `ℂ`-antilinear adjoint `B†` of a map `B`. -/
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
end adjoints

/-! ## Properties of Conjugations -/
section conj_push
variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- An antiunitary conjugation preserves the inner product up to a complex conjugate. -/
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

/-- An isometric `Conjugation` is antiunitary (proven via polarization identity). -/
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

/-- The Gâteaux derivative of `f` along `v` equals `Df[u] v`. -/
@[simp] lemma gateaux_at_zero_eq (f : H → W) (u v : H) (D : H →L[ℝ] W)
    (hf : HasRDerivAt f u D) :
    deriv (fun t : ℝ => f (u + t • v)) 0 = D v :=
  real_directional_deriv_eq (f:=f) (u:=u) (v:=v) (D:=D) hf

/-- Pointwise `ℂ`-linearity of `D₊`: `D₊(i•v) = i•(D₊ v)`. -/
@[simp] lemma Dplus_comm_J_point (f : H → W) (u v : H) :
    (DplusCLM (H:=H) (W:=W) f u) (J_H v)
      = (J_W) ((DplusCLM (H:=H) (W:=W) f u) v) := by
  have h := congrArg (fun (T : H →L[ℝ] W) => T v)
              (isCLinearR_Dplus (H:=H) (W:=W) f u)
  simpa [ContinuousLinearMap.comp_apply] using h.symm

/-- Pointwise `ℂ`-antilinearity of `D₋`: `D₋(i•v) = -i•(D₋ v)`. -/
@[simp] lemma Dminus_anticomm_J_point (f : H → W) (u v : H) :
    (DminusCLM (H:=H) (W:=W) f u) (J_H v)
      = - (J_W) ((DminusCLM (H:=H) (W:=W) f u) v) := by
  have h := congrArg (fun (T : H →L[ℝ] W) => T v)
              (isALinearR_Dminus (H:=H) (W:=W) f u)
  have h' := congrArg Neg.neg h
  simpa [ContinuousLinearMap.comp_apply, neg_neg] using h'.symm

/-- Pointwise Wirtinger split: `Df v = D₊ v + D₋ v`. -/
@[simp] lemma R_split_point (f : H → W) (u v : H) :
    fderivR (H:=H) (W:=W) f u v
      = DplusCLM (H:=H) (W:=W) f u v + DminusCLM (H:=H) (W:=W) f u v :=
  fderivR_apply_split (H:=H) (W:=W) f u v

/-- Riesz representation for `D₊`: `D₊ v = ⟪∇₊, v⟫`. -/
@[simp] lemma riesz_plus_point [CompleteSpace H] (f : H → ℂ) (u v : H) :
    DplusCLM (H:=H) (W:=ℂ) f u v
      = inner (𝕜 := ℂ) (gradPlus f u) v :=
  (inner_gradPlus_eq_Dplus (f:=f) (u:=u) (v:=v)).symm

/-- Riesz representation for `D₋`: `D₋ v = ⟪v, ∇₋⟫`. -/
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

/-- Hermitian adjoint identity for `ℂ`-linear maps: `⟪x, A y⟫ = ⟪A† x, y⟫`. -/
@[simp] lemma adjoint_linear_eq
  [CompleteSpace H] [CompleteSpace W]
  (A : H →L[ℂ] W) (x : W) (y : H) :
  inner (𝕜 := ℂ) x (A y) = inner (𝕜 := ℂ) ((ContinuousLinearMap.adjoint A) x) y := by simp

/-- Adjoint identity for `ℂ`-antilinear maps: `⟪x, B y⟫ = star ⟪B† x, y⟫`. -/
@[simp] lemma adjoint_antilinear_star
  [CompleteSpace H] [CompleteSpace W]
  (B : H → W)
  (h_add : ∀ y z, B (y + z) = B y + B z)
  (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
  (h_cont : Continuous B) (x : W) (y : H) :
  inner (𝕜 := ℂ) x (B y)
    = star (inner (𝕜 := ℂ) ((conjAdjoint B h_add h_smul h_cont) x) y) :=
  inner_eq_star_adjoint (B:=B) h_add h_smul h_cont x y

/-- An isometric `Conjugation` pushes through the inner product. -/
lemma conjugation_push_identity
    (C : Conjugation H) (hI : Conjugation.IsIsometry (V := H) C) (x y : H) :
    inner (𝕜 := ℂ) (C.C x) (C.C y)
      = star (inner (𝕜 := ℂ) x y)
      ∧ inner (𝕜 := ℂ) (C.C x) (C.C y)
      = inner (𝕜 := ℂ) y x := by
  have hA := Conjugation.isometry_to_antiunitary (V := H) C hI
  exact ⟨Conjugation.inner_conj_conj (C:=C) hA x y,
         Conjugation.inner_conj_conj_swap (C:=C) hA x y⟩

end Wirtinger
