import Mathlib
import WirtingerCalculus.Basic

/-!
First-order operation rules, star-based (no `Complex.conj`).

What this file provides:
* real-linear conjugation CLM `Cℂ : ℂ →L[ℝ] ℂ` defined via `star`
* `J` anti-commutes with `Cℂ`
* conjugation rules for `D₊`, `D₋` (both operator & directional forms)
* product / reciprocal / quotient rules (directional & gradient forms)
* formal partials on `ℂ` (`dz`, `dzbar`) and a 1D identity for `fderivR`
* directional chain rules for post-composition with a scalar map `g : ℂ → ℂ`

Only APIs used from your `Basic.lean`:
`Jc_apply`, `Jc_comp_Jc`, `R_split_point`, `Dplus_comm_J_point`,
`Dminus_anticomm_J_point`, `inner_gradPlus_eq_Dplus`,
`Dminus_eq_inner_gradMinus`, `fderivR_apply_split_grad`, `Aℒ_apply`.
-/

noncomputable section
open Complex Topology
open scoped ComplexInnerProductSpace

namespace Wirtinger

-- Notation shorthands used throughout
local notation "D₊" => DplusCLM
local notation "D₋" => DminusCLM
local notation "∇₊" => gradPlus
local notation "∇₋" => gradMinus

/-! ## Conjugation over `ℂ` as a real-linear CLM, via `star` -/

-- Keep `Complex.star_def` out of the default simp set; expand it only when needed.
attribute [-simp] Complex.star_def

/-- Real-linear complex conjugation on `ℂ`, implemented by `star`. -/
@[simp] def Cℂ : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := fun z => star z
  , map_add' := by simp [star_add]
  , map_smul' := by
      intro r z
      -- `star` reverses multiplication, and `star (r:ℂ) = r` for real `r`
      change star ((r : ℂ) * z) = (r : ℂ) * star z
      rw [star_mul, star_ofReal] }
, cont := continuous_star }

@[simp] lemma Cℂ_apply (z : ℂ) : Cℂ z = star z := rfl

/-- `J` anti-commutes with real-linear conjugation on `ℂ`. -/
lemma Jc_comp_Cℂ_anticom :
  (Jc ℂ).comp Cℂ = - (Cℂ.comp (Jc ℂ)) := by
  ext z
  -- LHS is `I * star z`, RHS is `- star (I * z)`
  simp [Jc_apply, Cℂ_apply, star_mul, star_I]

/-- Compatibility of the anti-twist with conjugation. -/
lemma Aℒ_comp_Cℂ
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  (T : H →L[ℝ] ℂ) :
  Aℒ (H:=H) (W:=ℂ) (Cℂ.comp T) = - Cℂ.comp (Aℒ (H:=H) (W:=ℂ) T) := by
  ext v
  -- Goal: I * star (T (I • v)) = - star (I * T (I • v))
  simp [Aℒ_apply, Cℂ_apply, ContinuousLinearMap.comp_apply, star_mul, star_I]

/-! ## Scalar-valued rules on a complex Hilbert space -/

section scalar_rules
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Conjugation (via `star`) -/

/-- Operator form: `D₊(star ∘ f) = Cℂ ∘L D₋ f`. -/
lemma Dplus_star_op (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) :
    D₊ (fun x => star (f x)) u = Cℂ.comp (D₋ f u) := by
  classical
  let D := fderivR f u
  have hDf : fderivR (fun x => star (f x)) u = Cℂ.comp D :=
    (Cℂ.hasFDerivAt.comp u hf.hasFDerivAt).fderiv
  -- Unfold `D₊` and `D₋`, use the compatibility of `Aℒ` with `Cℂ`.
  simp_rw [DplusCLM, DminusCLM, hDf, Aℒ_comp_Cℂ, sub_neg_eq_add,
           ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]

/-- Operator form: `D₋(star ∘ f) = Cℂ ∘L D₊ f`. -/
lemma Dminus_star_op (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) :
    D₋ (fun x => star (f x)) u = Cℂ.comp (D₊ f u) := by
  classical
  let D := fderivR f u
  have hDf : fderivR (fun x => star (f x)) u = Cℂ.comp D :=
    (Cℂ.hasFDerivAt.comp u hf.hasFDerivAt).fderiv
  simp_rw [DminusCLM, DplusCLM, hDf, Aℒ_comp_Cℂ,
           ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_smul]

/-- Directional forms. -/
@[simp] lemma Dplus_star_dir (f : H → ℂ) (u v : H) (hf : DifferentiableAt ℝ f u) :
  D₊ (fun x => star (f x)) u v = star (D₋ f u v) := by
  simpa using congrArg (fun L => L v) (Dplus_star_op f u hf)

@[simp] lemma Dminus_star_dir (f : H → ℂ) (u v : H) (hf : DifferentiableAt ℝ f u) :
  D₋ (fun x => star (f x)) u v = star (D₊ f u v) := by
  simpa using congrArg (fun L => L v) (Dminus_star_op f u hf)

/-! ### Product / reciprocal / quotient -/

section product_like
variable [CompleteSpace H]

/-- **Directional product rule** for `D₊`. -/
lemma Dplus_prod_dir (f g : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  D₊ (fun x => f x * g x) u v
    = D₊ f u v * g u + f u * D₊ g u v := by
  classical
  let Df := fderivR f u
  let Dg := fderivR g u
  let Dfg := fderivR (fun x => f x * g x) u
  have h_fderiv_eq : Dfg = f u • Dg + g u • Df := fderiv_mul hf hg
  have h_Dfg_v : Dfg v = f u * Dg v + g u * Df v := by
    simp [h_fderiv_eq]
  have h_Aℒ_fg_v :
      Aℒ (H:=H) (W:=ℂ) Dfg v
        = f u * Aℒ (H:=H) (W:=ℂ) Dg v + g u * Aℒ (H:=H) (W:=ℂ) Df v := by
    simp only [Aℒ_apply, smul_eq_mul]
    have h_at_Iv : Dfg (I • v) = f u * Dg (I • v) + g u * Df (I • v) := by
      simp [h_fderiv_eq]
    rw [h_at_Iv, mul_add]; ring
  -- Unfold `D₊` and substitute the two pointwise identities
  simp_rw [DplusCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
            h_Dfg_v, h_Aℒ_fg_v]
  ring

/-- **Directional product rule** for `D₋`. -/
lemma Dminus_prod_dir (f g : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  D₋ (fun x => f x * g x) u v
    = D₋ f u v * g u + f u * D₋ g u v := by
  classical
  let Df := fderivR f u
  let Dg := fderivR g u
  let Dfg := fderivR (fun x => f x * g x) u
  have h_fderiv_eq : Dfg = f u • Dg + g u • Df := fderiv_mul hf hg
  have h_Dfg_v : Dfg v = f u * Dg v + g u * Df v := by
    simp [h_fderiv_eq]
  have h_Aℒ_fg_v :
      Aℒ (H:=H) (W:=ℂ) Dfg v
        = f u * Aℒ (H:=H) (W:=ℂ) Dg v + g u * Aℒ (H:=H) (W:=ℂ) Df v := by
    simp only [Aℒ_apply, smul_eq_mul]
    have h_at_Iv : Dfg (I • v) = f u * Dg (I • v) + g u * Df (I • v) := by
      simp [h_fderiv_eq]
    rw [h_at_Iv, mul_add]; ring
  simp_rw [DminusCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
            h_Dfg_v, h_Aℒ_fg_v]
  ring

/-- **Gradient product rule.** -/
lemma grad_prod (f g : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  ∇₊ (fun x => f x * g x) u
    = star (g u) • ∇₊ f u + star (f u) • ∇₊ g u
∧ ∇₋ (fun x => f x * g x) u
    = g u • ∇₋ f u + f u • ∇₋ g u := by
  constructor
  · -- Compare via Riesz: inject through `toDual` and evaluate at an arbitrary `v`.
    apply (InnerProductSpace.toDual ℂ H).injective
    ext v
    rw [inner_gradPlus_eq_Dplus, Dplus_prod_dir f g u v hf hg, inner_add_left,
        inner_smul_left, star_star, inner_gradPlus_eq_Dplus, inner_gradPlus_eq_Dplus]
    ring
  · apply (InnerProductSpace.toDual ℂ H).injective
    ext v
    rw [Dminus_eq_inner_gradMinus, Dminus_prod_dir f g u v hf hg, inner_add_right,
        inner_smul_right, Dminus_eq_inner_gradMinus, Dminus_eq_inner_gradMinus]
    ring

end product_like

/-!  Congruence under `=ᶠ[𝓝 u]`. -/
section congr_helpers

lemma fderivR_congr_of_eventuallyEq
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  fderivR f u = fderivR g u := by
  -- Uniqueness of the Fréchet derivative + agreement near `u`
  have hf' := hf.hasFDerivAt
  have hg' := hg.hasFDerivAt
  have : HasFDerivAt g (fderivR f u) u := hf'.congr_of_eventuallyEq h.symm
  exact hg'.unique this

lemma DplusCLM_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  D₊ f u = D₊ g u := by
  rw [DplusCLM, DplusCLM, fderivR_congr_of_eventuallyEq hf hg h]

lemma DminusCLM_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  D₋ f u = D₋ g u := by
  rw [DminusCLM, DminusCLM, fderivR_congr_of_eventuallyEq hf hg h]

-- These gradient congruences use Riesz, so we assume completeness.
lemma gradPlus_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  ∇₊ f u = ∇₊ g u := by
  have hD := DplusCLM_congr_of_eventuallyEq hf hg h
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v; rw [riesz_plus_point, hD, ← riesz_plus_point]

lemma gradMinus_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  ∇₋ f u = ∇₋ g u := by
  have hD := DminusCLM_congr_of_eventuallyEq hf hg h
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v; rw [riesz_minus_point, hD, ← riesz_minus_point]

end congr_helpers

/-! ## Formal Wirtinger partials on `ℂ` -/

section partials_on_C
variable [CompleteSpace ℂ]

/-- `dz f z := D₊ f z 1`. -/
def dz (f : ℂ → ℂ) (z : ℂ) : ℂ := D₊ f z (1 : ℂ)

/-- `dzbar f z := D₋ f z 1`. -/
def dzbar (f : ℂ → ℂ) (z : ℂ) : ℂ := D₋ f z (1 : ℂ)

/-- 1D identity on `ℂ`:
`fderivR f u w = (dz f u) * w + (dzbar f u) * star w`. -/
lemma fderiv_via_partials (f : ℂ → ℂ) (u w : ℂ) :
  fderivR f u w = dz f u * w + dzbar f u * star w := by
  let D := fderivR f u
  have h_one : D 1 = dz f u + dzbar f u := by
    rw [R_split_point, dz, dzbar]
  have h_I : D I = I * dz f u - I * dzbar f u := by
    rw [R_split_point, Dplus_comm_J_point, Dminus_anticomm_J_point, Jc_apply]
    simp [dz, dzbar, smul_eq_mul, sub_eq_add_neg]
  -- Decompose w = w.re * 1 + w.im * I
  conv_lhs => rw [← re_add_im w, map_add, D.map_smul, D.map_smul, h_one, h_I]
  conv_rhs => rw [← re_add_im w, ← star_def]
  ring

end partials_on_C

/-! ## Quotient / inverse via gradients -/

section product_like
variable [CompleteSpace H]

/-- **Reciprocal rule** (pointwise nonvanishing). -/
lemma grad_inv (g : H → ℂ) (u : H)
    (hg : DifferentiableAt ℝ g u) (hgu : g u ≠ 0) :
  ∇₊ (fun x => (g x)⁻¹) u = - ((star (g u)) ^ 2)⁻¹ • ∇₊ g u
∧ ∇₋ (fun x => (g x)⁻¹) u = - ((g u) ^ 2)⁻¹ • ∇₋ g u := by
  have hg_inv : DifferentiableAt ℝ (fun x => (g x)⁻¹) u := hg.inv hgu
  -- product rule for g * g^{-1}
  have hprod := grad_prod g (fun x => (g x)⁻¹) u hg hg_inv
  -- `g * g^{-1} = 1` on a punctured neighborhood of `u`
  have h_eventually_one :
    (fun x => g x * (g x)⁻¹) =ᶠ[𝓝 u] (fun _ => (1 : ℂ)) := by
    filter_upwards [hg.continuousAt.eventually_ne hgu] with x hx
    simp [mul_inv_cancel hx]
  -- gradients of a constant are zero; use congruence helpers
  have h_const_plus : ∇₊ (fun _ : H => (1 : ℂ)) u = 0 := by
    apply (InnerProductSpace.toDual ℂ H).injective; ext v
    simp [inner_gradPlus_eq_Dplus, DplusCLM, fderiv_const]
  have h_const_minus : ∇₋ (fun _ : H => (1 : ℂ)) u = 0 := by
    apply (InnerProductSpace.toDual ℂ H).injective; ext v
    simp [Dminus_eq_inner_gradMinus, DminusCLM, fderiv_const]

  have h_left_plus :
      ∇₊ (fun x => g x * (g x)⁻¹) u = 0 :=
    gradPlus_congr_of_eventuallyEq (hg.mul hg_inv) (differentiableAt_const _) h_eventually_one
      |> Trans.trans (h_const_plus)
  have h_left_minus :
      ∇₋ (fun x => g x * (g x)⁻¹) u = 0 :=
    gradMinus_congr_of_eventuallyEq (hg.mul hg_inv) (differentiableAt_const _) h_eventually_one
      |> Trans.trans (h_const_minus)
  constructor
  · -- from product rule (plus side)
    have : 0
        = star ((g u)⁻¹) • ∇₊ g u
          + star (g u) • ∇₊ (fun x => (g x)⁻¹) u := by
      rw [h_left_plus] at hprod
      exact hprod.1
    -- isolate the unknown
    have hsolve :
        star (g u) • ∇₊ (fun x => (g x)⁻¹) u
          = - star ((g u)⁻¹) • ∇₊ g u := by
      rw [add_eq_zero_iff_eq_neg] at this; exact this
    -- cancel the factor `star (g u)` on the left
    have hne : star (g u) ≠ 0 := star_ne_zero.mpr hgu
    simpa [smul_smul, inv_smul_smul₀ hne, one_smul, star_inv, pow_two] using
      congr_arg (fun x => (star (g u))⁻¹ • x) hsolve
  · -- from product rule (minus side)
    have : 0
        = (g u)⁻¹ • ∇₋ g u
          + g u • ∇₋ (fun x => (g x)⁻¹) u := by
      rw [h_left_minus] at hprod
      exact hprod.2
    have hsolve :
        g u • ∇₋ (fun x => (g x)⁻¹) u
          = - (g u)⁻¹ • ∇₋ g u := by
      rw [add_eq_zero_iff_eq_neg] at this; exact this
    simpa [smul_smul, inv_smul_smul₀ hgu, one_smul, pow_two] using
      congr_arg (fun x => (g u)⁻¹ • x) hsolve

/-- **Quotient rule** (pointwise nonvanishing). -/
lemma grad_quot (f g : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (hgu : g u ≠ 0) :
  ∇₊ (fun x => f x / g x) u
    = ((star (g u)) ^ 2)⁻¹ • (star (g u) • ∇₊ f u - star (f u) • ∇₊ g u)
∧ ∇₋ (fun x => f x / g x) u
    = ((g u) ^ 2)⁻¹ • (g u • ∇₋ f u - f u • ∇₋ g u) := by
  have hg_inv : DifferentiableAt ℝ (fun x => (g x)⁻¹) u := hg.inv hgu
  have hinv := grad_inv (H:=H) g u hg hgu
  constructor
  · -- plus side
    have h_prod := (grad_prod f (fun x => (g x)⁻¹) u hf hg_inv).1
    rw [div_eq_mul_inv] at h_prod ⊢
    rw [h_prod, hinv.1]
    simp [smul_add, smul_smul, smul_sub, star_inv, pow_two]
    ring
  · -- minus side
    have h_prod := (grad_prod f (fun x => (g x)⁻¹) u hf hg_inv).2
    rw [div_eq_mul_inv] at h_prod ⊢
    rw [h_prod, hinv.2]
    simp [smul_add, smul_smul, smul_sub, pow_two]
    ring

end product_like

/-! ## Chain rules (directional) for post-composition by `g : ℂ → ℂ` -/

section chain_rules
variable [CompleteSpace H]

/-- Directional chain rule for `D₊` when postcomposing with `g : ℂ → ℂ`. -/
lemma Dplus_comp_scalar_dir
  (f : H → ℂ) (g : ℂ → ℂ) (u : H) (v : H)
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g (f u)) :
  D₊ (fun x => g (f x)) u v
    = dz g (f u) * D₊ f u v + dzbar g (f u) * star (D₋ f u v) := by
  classical
  let Df := fderivR f u
  let Dg := fderivR g (f u)
  have h_chain : fderivR (g ∘ f) u = Dg.comp Df :=
    (hg.hasFDerivAt.comp u hf.hasFDerivAt).fderiv
  -- 1D expansion of `Dg` on `ℂ`
  have h_Dg (w : ℂ) : Dg w = dz g (f u) * w + dzbar g (f u) * star w :=
    fderiv_via_partials g (f u) w
  -- Decompose `Df` at `v` and `I•v`
  have h_Df_v : Df v = D₊ f u v + D₋ f u v := by rw [R_split_point]
  have h_Df_Iv :
      Df (I • v) = I * D₊ f u v - I * D₋ f u v := by
    rw [R_split_point, Dplus_comm_J_point, Dminus_anticomm_J_point, Jc_apply]
    simp [smul_eq_mul, sub_eq_add_neg]
  -- Compute `D₊ (g ∘ f)` from the definition
  simp_rw [DplusCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, Aℒ_apply,
           ContinuousLinearMap.comp_apply, h_chain, h_Dg, h_Df_v, h_Df_Iv, smul_eq_mul, star_add, star_mul, star_I, star_sub]
  ring

/-- Directional chain rule for `D₋` when postcomposing with `g : ℂ → ℂ`. -/
lemma Dminus_comp_scalar_dir
  (f : H → ℂ) (g : ℂ → ℂ) (u : H) (v : H)
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g (f u)) :
  D₋ (fun x => g (f x)) u v
    = dzbar g (f u) * star (D₊ f u v) + dz g (f u) * D₋ f u v := by
  classical
  let Df := fderivR f u
  let Dg := fderivR g (f u)
  have h_chain : fderivR (g ∘ f) u = Dg.comp Df :=
    (hg.hasFDerivAt.comp u hf.hasFDerivAt).fderiv
  have h_Dg (w : ℂ) : Dg w = dz g (f u) * w + dzbar g (f u) * star w :=
    fderiv_via_partials g (f u) w
  have h_Df_v : Df v = D₊ f u v + D₋ f u v := by rw [R_split_point]
  have h_Df_Iv :
      Df (I • v) = I * D₊ f u v - I * D₋ f u v := by
    rw [R_split_point, Dplus_comm_J_point, Dminus_anticomm_J_point, Jc_apply]
    simp [smul_eq_mul, sub_eq_add_neg]
  simp_rw [DminusCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, Aℒ_apply,
           ContinuousLinearMap.comp_apply, h_chain, h_Dg, h_Df_v, h_Df_Iv, smul_eq_mul, star_add, star_mul, star_I, star_sub]
  ring

end chain_rules

end scalar_rules
end Wirtinger
