import Mathlib
import WirtingerCalculus.Basic

/-!
# First-Order Operation Rules for Wirtinger Calculus

This file adds fully expanded rules for:
* **Conjugation:** interaction of `D₊`, `D₋`, and gradients with complex conjugation.
* **Product / reciprocal / quotient** rules (for scalar-valued maps `H → ℂ`).
* **Chain rule** in gradient form for a composition `f ∘ g` with `g : H → V`, `f : V → ℂ`.
* **Formal Wirtinger partials on `ℂ`:** `∂/∂z` and `∂/∂\bar z` and an explicit `Df` formula.

It uses API established in `Basic.lean`, notably:
`DplusCLM`, `DminusCLM`, `gradPlus`, `gradMinus`,
`inner_gradPlus_eq_Dplus`, `Dminus_eq_inner_gradMinus`,
`fderivR_apply_split_grad`, `Dplus_add_Dminus`,
`Jc`, `J_H`, and the adjoint helpers
`adjoint_linear_eq`, `adjoint_antilinear_star`, and `conjAdjoint`.
-/

noncomputable section
open Complex
open scoped RealInnerProductSpace

namespace Wirtinger

/-- Short notations matching `Basic.lean`. -/
local notation "D₊" => DplusCLM
local notation "D₋" => DminusCLM
local notation "∇₊" => gradPlus
local notation "∇₋" => gradMinus

/-! ## Conjugation on `ℂ` as a real-linear CLM and its basic identity -/

/-- The canonical real-linear complex conjugation on `ℂ` as a continuous linear map. -/
@[simp] def Cℂ : ℂ →L[ℝ] ℂ :=
  Conjugation.toCLM ℂ standardConjugation

@[simp] lemma Cℂ_apply (z : ℂ) : Cℂ z = Complex.conj z := rfl

/-- `Jc` anti-commutes with conjugation on `ℂ` at the operator level:
`(Jc ℂ) ∘ Cℂ = (-Cℂ) ∘ (Jc ℂ)`. -/
lemma Jc_comp_Cℂ_anticom :
    (Jc ℂ).comp Cℂ = (-Cℂ).comp (Jc ℂ) := by
  -- Reduce to the scalar identity `C ((i) • z) = - i • C z`.
  ext z
  simp [ContinuousLinearMap.comp_apply, Cℂ, Conjugation.toCLM, Jc_apply,
        standardConjugation, Conjugation.antiJ_apply, neg_smul, smul_neg]

/-! ## Scalar-valued rules on a complex Hilbert space -/

section scalar_rules

variables {H V : Type*}
variables [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variables [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ### Conjugation rules -/

/-- Directional rule: `D₊(conj ∘ f) = Cℂ ∘ D₋ f` (operator level).
We assume `f` is real-differentiable at `u` to use the chain rule for `fderiv`. -/
lemma Dplus_conj_op (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) :
    D₊ (fun x => Complex.conj (f x)) u = Cℂ ∘L D₋ f u := by
  classical
  -- Real-chain rule for the Fréchet derivative:
  have hDf :
      fderivR (H:=H) (W:=ℂ) (fun x => Complex.conj (f x)) u
        = Cℂ ∘L fderivR (H:=H) (W:=ℂ) f u := by
    have hconj : HasFDerivAt (fun z : ℂ => Cℂ z) Cℂ (f u) := (Cℂ.hasFDerivAt (x := f u))
    have hf'   : HasFDerivAt f (fderivR (H:=H) (W:=ℂ) f u) u := hf.hasFDerivAt
    simpa [fderivR, ContinuousLinearMap.comp_apply]
      using (hconj.comp u hf').fderiv
  -- Unfold `D₊` and use `(Jc ℂ) ∘ Cℂ = (-Cℂ) ∘ (Jc ℂ)`.
  ext v
  have := congrArg (fun (T : H →L[ℝ] ℂ) => T v)
    (by
      simpa [DplusCLM, one_div, hDf, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
             ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
             ContinuousLinearMap.comp_assoc, Jc_comp_Cℂ_anticom,
             sub_eq_add_neg, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg] )
  -- RHS simplifies to `Cℂ (D₋ f u v)`.
  simpa [ContinuousLinearMap.comp_apply]

/-- Directional rule: `D₋(conj ∘ f) = Cℂ ∘ D₊ f` (operator level). -/
lemma Dminus_conj_op (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) :
    D₋ (fun x => Complex.conj (f x)) u = Cℂ ∘L D₊ f u := by
  classical
  have hDf :
      fderivR (H:=H) (W:=ℂ) (fun x => Complex.conj (f x)) u
        = Cℂ ∘L fderivR (H:=H) (W:=ℂ) f u := by
    have hconj : HasFDerivAt (fun z : ℂ => Cℂ z) Cℂ (f u) := (Cℂ.hasFDerivAt (x := f u))
    have hf'   : HasFDerivAt f (fderivR (H:=H) (W:=ℂ) f u) u := hf.hasFDerivAt
    simpa [fderivR, ContinuousLinearMap.comp_apply]
      using (hconj.comp u hf').fderiv
  ext v
  have := congrArg (fun (T : H →L[ℝ] ℂ) => T v)
    (by
      simpa [DminusCLM, one_div, hDf, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
             ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
             ContinuousLinearMap.comp_assoc, Jc_comp_Cℂ_anticom,
             add_comm, add_left_comm, add_assoc,
             sub_eq_add_neg, ContinuousLinearMap.neg_comp, ContinuousLinearMap.comp_neg] )
  simpa [ContinuousLinearMap.comp_apply]

/-- Pointwise forms. -/
@[simp] lemma Dplus_conj_dir (f : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) :
    D₊ (fun x => Complex.conj (f x)) u v = Complex.conj (D₋ f u v) := by
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun (T : H →L[ℝ] ℂ) => T v) (Dplus_conj_op (f:=f) (u:=u) hf)

@[simp] lemma Dminus_conj_dir (f : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) :
    D₋ (fun x => Complex.conj (f x)) u v = Complex.conj (D₊ f u v) := by
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun (T : H →L[ℝ] ℂ) => T v) (Dminus_conj_op (f:=f) (u:=u) hf)

/-- Conjugation: gradient-level consequences. -/
@[simp] lemma grad_conj (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) [CompleteSpace H] :
    ∇₊ (fun x => Complex.conj (f x)) u = ∇₋ f u ∧
    ∇₋ (fun x => Complex.conj (f x)) u = ∇₊ f u := by
  classical
  constructor
  · -- `⟪LHS, v⟫ = D₊(conj f)[v] = conj (D₋ f [v]) = ⟪∇₋ f, v⟫`
    apply InnerProductSpace.ext_inner_right ℂ; intro v
    simpa [Dminus_eq_inner_gradMinus] using (Dplus_conj_dir (f:=f) (u:=u) (v:=v) hf)
  · -- `⟪v, LHS⟫ = D₋(conj f)[v] = conj (D₊ f [v]) = ⟪v, ∇₊ f⟫`
    apply InnerProductSpace.ext_inner_left ℂ; intro v
    simpa [inner_gradPlus_eq_Dplus] using (Dminus_conj_dir (f:=f) (u:=u) (v:=v) hf)

/-! ### Product / reciprocal / quotient rules (scalar-valued) -/

section product_rules
variable [CompleteSpace H]

/-- **Product rule:** for `f g : H → ℂ` real-differentiable at `u`. -/
lemma grad_prod (f g : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
    ∇₊ (fun x => f x * g x) u
      = Complex.conj (g u) • ∇₊ f u + Complex.conj (f u) • ∇₊ g u
  ∧ ∇₋ (fun x => f x * g x) u
      = (g u) • ∇₋ f u + (f u) • ∇₋ g u := by
  classical
  constructor
  · -- (+) via inner characterization
    apply InnerProductSpace.ext_inner_right ℂ; intro v
    -- real product rule on `fderiv`
    have hprod :
      fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u v
        = fderivR (H:=H) (W:=ℂ) f u v * g u
          + f u * fderivR (H:=H) (W:=ℂ) g u v := by
      simpa using
        congrArg (fun (T : H →L[ℝ] ℂ) => T v)
          ((hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv)
    -- extract the (+)-part via `inner_gradPlus_eq_Dplus`
    -- `D₊(fg)[v] = conj(g u) ⟪∇₊ f, v⟫ + conj(f u) ⟪∇₊ g, v⟫`
    -- this follows from the defs of `D₊` and the above `hprod`
    -- but we can shortcut by: split `fderiv` and compare
    have := fderivR_apply_split_grad (H:=H) (f:=fun x => f x * g x) (u:=u) (v:=v)
    -- Rewrite RHS using `hprod`, then compare coefficients on the (+) side.
    -- It becomes a simple `simp` using `inner_*` and linearity.
    -- left side (+) is `⟪∇₊(fg), v⟫`.
    -- right side (+) contributes `conj(g u) ⟪∇₊ f, v⟫ + conj(f u) ⟪∇₊ g, v⟫`.
    have hf_split := fderivR_apply_split_grad (H:=H) (f:=f) (u:=u) (v:=v)
    have hg_split := fderivR_apply_split_grad (H:=H) (f:=g) (u:=u) (v:=v)
    -- finish:
    simp [hprod, inner_gradPlus_eq_Dplus, Dminus_eq_inner_gradMinus,
          inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
          mul_comm, mul_left_comm, mul_assoc] at this
    -- Now equate the (+)-parts:
    -- `⟪∇₊(fg), v⟫ = conj(g u) ⟪∇₊ f, v⟫ + conj(f u) ⟪∇₊ g, v⟫`
    simpa [inner_add_left, inner_smul_left]
  · -- (−) via inner characterization
    apply InnerProductSpace.ext_inner_left ℂ; intro v
    have hprod :
      fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u v
        = fderivR (H:=H) (W:=ℂ) f u v * g u
          + f u * fderivR (H:=H) (W:=ℂ) g u v := by
      simpa using
        congrArg (fun (T : H →L[ℝ] ℂ) => T v)
          ((hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv)
    have := fderivR_apply_split_grad (H:=H) (f:=fun x => f x * g x) (u:=u) (v:=v)
    simp [hprod, inner_gradPlus_eq_Dplus, Dminus_eq_inner_gradMinus,
          inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
          mul_comm, mul_left_comm, mul_assoc] at this
    -- `⟪v, ∇₋(fg)⟫ = (g u) ⟪v, ∇₋ f⟫ + (f u) ⟪v, ∇₋ g⟫`
    simpa [inner_add_right, inner_smul_right]

/-- **Reciprocal rule** (under `g u ≠ 0`). -/
lemma grad_inv (g : H → ℂ) (u : H)
    (hg : DifferentiableAt ℝ g u) (h : g u ≠ 0) [CompleteSpace H] :
    ∇₊ (fun x => (g x)⁻¹) u = - (Complex.conj (g u))⁻² • ∇₊ g u
  ∧ ∇₋ (fun x => (g x)⁻¹) u = - (g u)⁻² • ∇₋ g u := by
  classical
  -- Use product identity: `g * (g⁻¹) = 1`, and the product rule.
  have hconst₊ : ∇₊ (fun _ : H => (1 : ℂ)) u = 0 := by simpa
  have hconst₋ : ∇₋ (fun _ : H => (1 : ℂ)) u = 0 := by simpa
  have hp := (grad_prod (f := g) (g := fun x => (g x)⁻¹) (u := u)
    (hf := hg) (hg := (hg.inv h)) )
  have t : g u * (g u)⁻¹ = (1 : ℂ) := by field_simp
  constructor
  · have := hp.1
    simpa [t, hconst₊, smul_add, add_comm, add_left_comm, add_assoc,
           Complex.conj_inv, one_div, pow_two, inv_mul_cancel h,
           mul_comm, mul_left_comm, mul_assoc]
      using this
  · have := hp.2
    simpa [t, hconst₋, smul_add, add_comm, add_left_comm, add_assoc,
           one_div, pow_two, inv_mul_cancel h, mul_comm, mul_left_comm, mul_assoc]
      using this

/-- **Quotient rule** (under `g u ≠ 0`). -/
lemma grad_quot (f g : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
    (h : g u ≠ 0) [CompleteSpace H] :
    ∇₊ (fun x => f x / g x) u
      = Complex.conj (g u)⁻² • (Complex.conj (g u) • ∇₊ f u - Complex.conj (f u) • ∇₊ g u)
  ∧ ∇₋ (fun x => f x / g x) u
      = (g u)⁻² • ((g u) • ∇₋ f u - (f u) • ∇₋ g u) := by
  classical
  have hinv := grad_inv (g := g) (u := u) (hg := hg) (h := h)
  constructor
  · have := (grad_prod (f := f) (g := fun x => (g x)⁻¹) (u := u)
      (hf := hf) (hg := (hg.inv h))).1
    simpa [mul_comm, mul_left_comm, mul_assoc, smul_sub, mul_smul,
           Complex.conj_inv, hinv.1] using this
  · have := (grad_prod (f := f) (g := fun x => (g x)⁻¹) (u := u)
      (hf := hf) (hg := (hg.inv h))).2
    simpa [mul_comm, mul_left_comm, mul_assoc, smul_sub, mul_smul, hinv.2] using this

end product_rules

/-! ### Chain rule in gradient form -/

section chain_rule
variables [CompleteSpace H] [CompleteSpace V]

/-- Upgrade `D₊ g u : H →L[ℝ] V` to a `ℂ`-linear CLM so we can use the usual adjoint. -/
def Dplus_asCLM (g : H → V) (u : H) : H →L[ℂ] V :=
{ toLinearMap :=
  { toFun := fun v => D₊ (H:=H) (W:=V) g u v
  , map_add' := by intro x y; simp
  , map_smul' := by
      intro a v
      set D := D₊ (H := H) (W := V) g u
      -- Use the same real/imag split trick as in `Basic.lean`:
      have h_smul₁ : ((a.re : ℝ) • v + a.im • (J_H v)) = a • v := by
        change ((a.re : ℂ) • v + ((a.im : ℂ) * I) • v) = a • v
        simp [mul_comm, add_comm, add_left_comm, add_assoc, add_smul, smul_add, smul_smul,
              Complex.ofReal_im, Complex.ofReal_re, Complex.re_add_im, Complex.ofReal_mul,
              Complex.ofReal_sub, Complex.ofReal_one, Complex.I_mul, Complex.mul_I]
      have h_comm : D (J_H v) = (J_W) (D v) := by
        simpa using (Dplus_comm_J_point (H:=H) (W:=V) (f:=g) (u:=u) (v:=v)).symm
      have h_smul₂ :
          ((a.re : ℝ) • D v + a.im • (J_W) (D v)) = a • D v := by
        change ((a.re : ℂ) • D v + ((a.im : ℂ) * I) • D v) = a • D v
        simp [mul_comm, add_comm, add_left_comm, add_assoc, add_smul, smul_add, smul_smul,
              Complex.ofReal_im, Complex.ofReal_re, Complex.re_add_im, Complex.ofReal_mul,
              Complex.ofReal_sub, Complex.ofReal_one, Complex.I_mul, Complex.mul_I]
      calc
        D ((a : ℝ) • v) = D ((a.re : ℝ) • v + a.im • (J_H v)) := by
          simpa [algebraMap.coe_smul]
      _ = (a.re : ℝ) • D v + a.im • D (J_H v) := by simp [map_add, map_smul]
      _ = (a.re : ℝ) • D v + a.im • (J_W) (D v) := by simpa [h_comm]
      _ = by simpa [map_add, map_smul, h_smul₁, h_smul₂] }
, cont := (D₊ (H:=H) (W:=V) g u).continuous }

/-- Build the antilinear adjoint input from `D₋ g u`. -/
def conjAdjoint_Dminus (g : H → V) (u : H) : V → H :=
  conjAdjoint
    (B := fun v : H => D₋ (H:=H) (W:=V) g u v)
    (by intro y z; simp) -- additivity
    (by -- antilinearity over `ℂ`
      intro a y
      -- like in `Basic.lean` we use the `J` anti-commutation to derive full `ℂ`-antilinearity
      set D := D₋ (H:=H) (W:=V) g u
      have h_smul₁ : ((a.re : ℝ) • y + a.im • (J_H y)) = a • y := by
        change ((a.re : ℂ) • y + ((a.im : ℂ) * I) • y) = a • y
        simp [mul_comm, add_comm, add_left_comm, add_assoc, add_smul, smul_add, smul_smul,
              Complex.ofReal_im, Complex.ofReal_re, Complex.re_add_im, Complex.ofReal_mul,
              Complex.ofReal_sub, Complex.ofReal_one, Complex.I_mul, Complex.mul_I]
      have h_anti : D (J_H y) = - (J_W) (D y) := by
        simpa using (Dminus_anticomm_J_point (H:=H) (W:=V) (f:=g) (u:=u) (v:=y))
      -- now compute:
      calc
        D ((a : ℝ) • y)
            = D ((a.re : ℝ) • y + a.im • (J_H y)) := by
                simpa [algebraMap.coe_smul]
        _   = (a.re : ℝ) • D y + a.im • D (J_H y) := by simp [map_add, map_smul]
        _   = (a.re : ℝ) • D y + a.im • (-(J_W) (D y)) := by simpa [h_anti]
        _   = ((a.re : ℂ) • D y) + (((a.im : ℂ) * (-I)) • D y) := by simp
        _   = ((a.re : ℂ) - (a.im : ℂ) * I) • D y := by
                simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, sub_smul, smul_add, mul_comm]
        _   = (star a) • D y := by
                simp [star_eq_re_sub_im, sub_eq_add_neg]
      )
    ((D₋ (H:=H) (W:=V) g u).continuous) -- continuity

/-- **Chain rule (gradient form)** for `f ∘ g`. -/
lemma chain_rule
  (g : H → V) (f : V → ℂ) (u : H)
  (hg : DifferentiableAt ℝ g u) (hf : DifferentiableAt ℝ f (g u))
  [CompleteSpace H] [CompleteSpace V] :
  let A := Dplus_asCLM (H:=H) (g:=g) u
  let B := fun v : H => D₋ (H:=H) (W:=V) g u v
  let p := ∇₊ f (g u)
  let q := ∇₋ f (g u)
  (∇₊ (fun x => f (g x)) u = (ContinuousLinearMap.adjoint A) p + (conjAdjoint_Dminus (H:=H) (g:=g) u) q)
∧ (∇₋ (fun x => f (g x)) u = (conjAdjoint_Dminus (H:=H) (g:=g) u) p + (ContinuousLinearMap.adjoint A) q) := by
  classical
  intro A B p q; constructor
  · -- (+) part
    apply InnerProductSpace.ext_inner_right ℂ; intro v
    -- Real chain rule on `fderiv`:
    have hcomp :
      fderivR (H:=H) (W:=ℂ) (fun x => f (g x)) u v
        = fderivR (H:=V) (W:=ℂ) f (g u)
            (fderivR (H:=H) (W:=V) g u v) := by
      simpa using
        congrArg (fun (T : H →L[ℝ] ℂ) => T v)
          ((hf.hasFDerivAt.comp u hg.hasFDerivAt).fderiv)
    -- Riesz split for `f` at `g u`
    have hfW (w : V) :
      fderivR (H:=V) (W:=ℂ) f (g u) w
        = inner (𝕜 := ℂ) (∇₊ f (g u)) w + inner (𝕜 := ℂ) w (∇₋ f (g u)) :=
      fderivR_apply_split_grad (H:=V) (f:=f) (u:=g u) (v:=w)
    -- Split `Dg` into `D₊ + D₋` pointwise:
    have hsplit :
      fderivR (H:=H) (W:=V) g u v = D₊ g u v + D₋ g u v := by
      simpa using (R_split_point (H:=H) (W:=V) (f:=g) (u:=u) (v:=v))
    -- Combine:
    have := fderivR_apply_split_grad (H:=H) (f:=fun x => f (g x)) (u:=u) (v:=v)
    -- Rewrite RHS with `hcomp`, `hfW`, `hsplit`, then linear/antilinear adjoint identities:
    -- (+)-terms are `⟪p, D₊ v⟫` and `⟪D₋ v, q⟫`.
    -- `⟪p, D₊ v⟫ = ⟪(A†) p, v⟫`, and `⟪D₋ v, q⟫ = ⟪(conjAdjoint_Dminus) q, v⟫`.
    have : inner (𝕜 := ℂ) (∇₊ (fun x => f (g x)) u) v
            = inner (𝕜 := ℂ) ((ContinuousLinearMap.adjoint A) p) v
              + inner (𝕜 := ℂ) ((conjAdjoint_Dminus (H:=H) (g:=g) u) q) v := by
      -- start from the master split equality:
      have := fderivR_apply_split_grad (H:=H) (f:=fun x => f (g x)) (u:=u) (v:=v)
      -- rewrite via chain rule and split for `f` and `g`
      simpa [hcomp, hsplit, hfW, map_add, inner_add_left, inner_add_right,
             inner_map_adjoint_left, inner_map_adjoint_right,
             ContinuousLinearMap.comp_apply,
             -- turn `⟪D₋ v, q⟫` into `⟪(conjAdjoint_Dminus) q, v⟫`
             inner_conj_symm, adjoint_antilinear_star]
    simpa [inner_add_left]
  · -- (−) part
    apply InnerProductSpace.ext_inner_left ℂ; intro v
    -- the other two terms become `⟪v, (conjAdjoint_Dminus) p⟫ + ⟪v, (A†) q⟫`.
    have hcomp :
      fderivR (H:=H) (W:=ℂ) (fun x => f (g x)) u v
        = fderivR (H:=V) (W:=ℂ) f (g u)
            (fderivR (H:=H) (W:=V) g u v) := by
      simpa using
        congrArg (fun (T : H →L[ℝ] ℂ) => T v)
          ((hf.hasFDerivAt.comp u hg.hasFDerivAt).fderiv)
    have hfW (w : V) :
      fderivR (H:=V) (W:=ℂ) f (g u) w
        = inner (𝕜 := ℂ) p w + inner (𝕜 := ℂ) w q :=
      fderivR_apply_split_grad (H:=V) (f:=f) (u:=g u) (v:=w)
    have hsplit :
      fderivR (H:=H) (W:=V) g u v = D₊ g u v + D₋ g u v := by
      simpa using (R_split_point (H:=H) (W:=V) (f:=g) (u:=u) (v:=v))
    have : inner (𝕜 := ℂ) v (∇₋ (fun x => f (g x)) u)
            = inner (𝕜 := ℂ) v ((conjAdjoint_Dminus (H:=H) (g:=g) u) p
                                 + (ContinuousLinearMap.adjoint A) q) := by
      -- from the same expansion but collecting the other two terms
      have := fderivR_apply_split_grad (H:=H) (f:=fun x => f (g x)) (u:=u) (v:=v)
      simpa [hcomp, hsplit, hfW, map_add, inner_add_left, inner_add_right,
             inner_map_adjoint_left, inner_map_adjoint_right,
             inner_conj_symm, adjoint_antilinear_star,
             add_comm, add_left_comm, add_assoc]
    simpa

end chain_rule

/-! ## Formal Wirtinger partials on `ℂ` -/

section partials_on_C
variable [CompleteSpace ℂ]

/-- `∂/∂z` as the (+)-directional derivative along `1`. -/
def ∂z (f : ℂ → ℂ) (z : ℂ) : ℂ := D₊ (H:=ℂ) (W:=ℂ) f z (1 : ℂ)

/-- `∂/∂\bar z` as the (−)-directional derivative along `1`. -/
def ∂zbar (f : ℂ → ℂ) (z : ℂ) : ℂ := D₋ (H:=ℂ) (W:=ℂ) f z (1 : ℂ)

/-- On `ℂ` (with the standard inner product linear in the first argument):
`∇₊ f z = ∂z f z` and `∂zbar f z = conj (∇₋ f z)`. -/
lemma grads_vs_partials (f : ℂ → ℂ) (z : ℂ) :
    (∇₊ f z = ∂z f z) ∧ (∂zbar f z = Complex.conj (∇₋ f z)) := by
  constructor
  · -- `∂z f z = D₊ f z 1 = ⟪∇₊ f z, 1⟫ = ∇₊ f z`
    -- because for `ℂ`, `inner x 1 = x`.
    have := (inner_gradPlus_eq_Dplus (H:=ℂ) (f:=f) (u:=z) (v:=(1:ℂ)))
    -- RHS is `⟪∇₊,1⟫`; `simp` knows `inner x (1:ℂ) = x`.
    simpa [∂z, inner_gradPlus_eq_Dplus]
      using this.symm
  · -- `∂zbar f z = D₋ f z 1 = ⟪1, ∇₋ f z⟫ = conj (∇₋ f z)`
    have := (Dminus_eq_inner_gradMinus (H:=ℂ) (f:=f) (u:=z) (v:=(1:ℂ)))
    -- `inner 1 x = conj x` on `ℂ`.
    simpa [∂zbar] using this

/-- Textbook 1D identity on `ℂ`:
`Df[u] w = (∂z f u) * conj w + w * (∂\bar z f u)`. -/
lemma fderiv_via_partials (f : ℂ → ℂ) (u w : ℂ) :
  fderivR (H:=ℂ) (W:=ℂ) f u w
    = (∂z f u) * Complex.conj w + w * (∂zbar f u) := by
  -- Start from the general split via gradients, then substitute partials.
  have := fderivR_apply_split_grad (H:=ℂ) (f:=f) (u:=u) (v:=w)
  rcases (grads_vs_partials (f:=f) (z:=u)) with ⟨h₊, h₋⟩
  -- `inner (∇₊, w) = (∂z) * conj w` and `inner w (∇₋) = w * conj (∇₋) = w * ∂zbar`
  simpa [h₊, h₋, Complex.conj_mul, Complex.conj_conj]

end partials_on_C

end scalar_rules
end Wirtinger
