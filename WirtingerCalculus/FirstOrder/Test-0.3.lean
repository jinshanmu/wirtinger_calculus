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
  , map_add' := by intro z w; simp
  , map_smul' := by
      intro r z
      -- `star` reverses multiplication, and `star (r:ℂ) = r` for real `r`
      change star ((r : ℂ) * z) = (r : ℂ) * star z
      have : star ((r : ℂ) * z) = star z * (r : ℂ) := by
        simp [star_mul]
      simp }
, cont := continuous_star }

@[simp] lemma Cℂ_apply (z : ℂ) : Cℂ z = star z := rfl

/-- `J` anti-commutes with real-linear conjugation on `ℂ`. -/
lemma Jc_comp_Cℂ_anticom :
  (Jc ℂ).comp Cℂ = - (Cℂ.comp (Jc ℂ)) := by
  ext z
  -- LHS is `I * star z`, RHS is `- star (I * z)`
  simp [Jc_apply, Cℂ_apply, star_mul, Complex.star_def,
        mul_comm, mul_left_comm, mul_assoc]

/-- Compatibility of the anti-twist with conjugation. -/
lemma Aℒ_comp_Cℂ
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  (T : H →L[ℝ] ℂ) :
  Aℒ (H:=H) (W:=ℂ) (Cℂ.comp T) = - Cℂ.comp (Aℒ (H:=H) (W:=ℂ) T) := by
  ext v
  -- `Aℒ_apply` comes from your `Basic.lean`: `Aℒ T v = I * T (I • v)`
  simp [Aℒ_apply, Cℂ_apply, ContinuousLinearMap.comp_apply,
        star_mul, Complex.star_def,
        mul_comm, mul_left_comm, mul_assoc]

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
  -- Unfold `D₊` and use the compatibility of `Aℒ` with `Cℂ`.
  simp [DplusCLM, hDf, Aℒ_comp_Cℂ, sub_eq_add_neg]

/-- Operator form: `D₋(star ∘ f) = Cℂ ∘L D₊ f`. -/
lemma Dminus_star_op (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) :
    D₋ (fun x => star (f x)) u = Cℂ.comp (D₊ f u) := by
  classical
  let D := fderivR f u
  have hDf : fderivR (fun x => star (f x)) u = Cℂ.comp D :=
    (Cℂ.hasFDerivAt.comp u hf.hasFDerivAt).fderiv
  simp [DminusCLM, hDf, Aℒ_comp_Cℂ, sub_eq_add_neg, add_comm]

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
    simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      using congrArg (fun L => L v) h_fderiv_eq
  have h_Aℒ_fg_v :
      Aℒ (H:=H) (W:=ℂ) Dfg v
        = f u * Aℒ (H:=H) (W:=ℂ) Dg v + g u * Aℒ (H:=H) (W:=ℂ) Df v := by
    -- `Aℒ T v = I * T (I • v)` in the scalar codomain
    simp [Aℒ_apply, h_Dfg_v, mul_add, mul_assoc]
  -- Unfold `D₊` and substitute the two pointwise identities
  simp [DplusCLM, h_Dfg_v, h_Aℒ_fg_v]

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
    simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      using congrArg (fun L => L v) h_fderiv_eq
  have h_Aℒ_fg_v :
      Aℒ (H:=H) (W:=ℂ) Dfg v
        = f u * Aℒ (H:=H) (W:=ℂ) Dg v + g u * Aℒ (H:=H) (W:=ℂ) Df v := by
    simp [Aℒ_apply, h_Dfg_v, mul_add, mul_assoc]
  simp [DminusCLM, h_Dfg_v, h_Aℒ_fg_v]

/-- **Gradient product rule.** -/
lemma grad_prod (f g : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  ∇₊ (fun x => f x * g x) u
    = star (g u) • ∇₊ f u + star (f u) • ∇₊ g u
∧ ∇₋ (fun x => f x * g x) u
    = g u • ∇₋ f u + f u • ∇₋ g u := by
  constructor
  ·
    -- Compare via Riesz: inject through `toDual` and evaluate at an arbitrary `v`.
    apply (InnerProductSpace.toDual ℂ H).injective
    ext v
    simp [inner_gradPlus_eq_Dplus, Dplus_prod_dir f g u v hf hg]
  ·
    apply (InnerProductSpace.toDual ℂ H).injective
    ext v
    simp [Dminus_eq_inner_gradMinus, Dminus_prod_dir f g u v hf hg]

end product_like

/-!  Congruence under `=ᶠ[𝓝 u]`. -/
section congr_helpers

private lemma fderivR_congr_of_eventuallyEq
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  (f g : H → ℂ) (u : H)
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  fderivR f u = fderivR g u := by
  -- Uniqueness of the Fréchet derivative + agreement near `u`
  have hf' := hf.hasFDerivAt
  have hg' := hg.hasFDerivAt
  have : HasFDerivAt g (fderivR f u) u := hf'.congr_of_eq (by simpa using h.symm)
  exact (hg'.unique this)

lemma DplusCLM_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  D₊ f u = D₊ g u := by
  have := fderivR_congr_of_eventuallyEq (H:=H) f g u hf hg h
  simp [DplusCLM, this]

lemma DminusCLM_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  D₋ f u = D₋ g u := by
  have := fderivR_congr_of_eventuallyEq (H:=H) f g u hf hg h
  simp [DminusCLM, this]

-- These gradient congruences use Riesz, so we assume completeness.
lemma gradPlus_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  ∇₊ f u = ∇₊ g u := by
  have hD := DplusCLM_congr_of_eventuallyEq (H:=H) hf hg h
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v; simp [riesz_plus_point, hD]

lemma gradMinus_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  ∇₋ f u = ∇₋ g u := by
  have hD := DminusCLM_congr_of_eventuallyEq (H:=H) hf hg h
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v; simp [riesz_minus_point, hD]

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
  -- Split via your scalar identity
  have hsplit := fderivR_apply_split_grad (H:=ℂ) (f:=f) (u:=u) (v:=w)
  -- `⟪∇₊, w⟫ = w * ⟪∇₊, 1⟫ = (dz f u) * w`
  have hplus :
      ⟪∇₊ (H:=ℂ) (W:=ℂ) f u, w⟫ = dz f u * w := by
    simpa [dz, inner_gradPlus_eq_Dplus, Algebra.smul_def, one_mul, mul_comm]
      using (inner_smul_right (∇₊ (H:=ℂ) (W:=ℂ) f u) (1 : ℂ) w)
  -- `⟪w, ∇₋⟫ = star w * ⟪1, ∇₋⟫ = (dzbar f u) * star w`
  have hminus :
      ⟪w, ∇₋ (H:=ℂ) (W:=ℂ) f u⟫ = dzbar f u * star w := by
    -- conjugate linear in the first slot
    simpa [dzbar, Dminus_eq_inner_gradMinus, Algebra.smul_def, one_mul, mul_comm, mul_left_comm]
      using (inner_smul_left (1 : ℂ) (∇₋ (H:=ℂ) (W:=ℂ) f u) w)
  -- Put both together
  simpa [hplus, hminus] using hsplit

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
    simpa [hx] using (mul_inv_cancel hx)
  -- gradients of a constant are zero; use congruence helpers
  have h_const_plus : ∇₊ (fun _ : H => (1 : ℂ)) u = 0 := by
    apply (InnerProductSpace.toDual ℂ H).injective; ext v
    simp [inner_gradPlus_eq_Dplus, DplusCLM, fderiv_const]
  have h_const_minus : ∇₋ (fun _ : H => (1 : ℂ)) u = 0 := by
    apply (InnerProductSpace.toDual ℂ H).injective; ext v
    simp [Dminus_eq_inner_gradMinus, DminusCLM, fderiv_const]

  have h_left_plus :
      ∇₊ (fun x => g x * (g x)⁻¹) u = 0 := by
    simpa [h_const_plus]
      using gradPlus_congr_of_eventuallyEq (H:=H)
            (hf := (hg.mul hg_inv))
            (hg := differentiableAt_const) h_eventually_one
  have h_left_minus :
      ∇₋ (fun x => g x * (g x)⁻¹) u = 0 := by
    simpa [h_const_minus]
      using gradMinus_congr_of_eventuallyEq (H:=H)
            (hf := (hg.mul hg_inv))
            (hg := differentiableAt_const) h_eventually_one
  constructor
  ·
    -- from product rule (plus side)
    have : 0
        = star ((g u)⁻¹) • ∇₊ g u
          + star (g u) • ∇₊ (fun x => (g x)⁻¹) u := by
      simpa [h_left_plus] using hprod.1
    -- isolate the unknown
    have hsolve :
        star (g u) • ∇₊ (fun x => (g x)⁻¹) u
          = - star ((g u)⁻¹) • ∇₊ g u := by
      simpa [add_comm, add_left_comm, add_assoc, smul_add, smul_neg] using this
    -- cancel the factor `star (g u)` on the left
    have hne : star (g u) ≠ 0 := star_ne_zero.mpr hgu
    have hID : (star (g u))⁻¹ * star (g u) = 1 := by
      simpa using inv_mul_cancel hne
    have := congrArg (fun x => (star (g u))⁻¹ • x) hsolve
    -- simplify coefficients, using `star_inv`
    simpa [smul_smul, hID, one_smul, star_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
      using this
  ·
    -- from product rule (minus side)
    have : 0
        = (g u)⁻¹ • ∇₋ g u
          + g u • ∇₋ (fun x => (g x)⁻¹) u := by
      simpa [h_left_minus] using hprod.2
    have hsolve :
        g u • ∇₋ (fun x => (g x)⁻¹) u
          = - (g u)⁻¹ • ∇₋ g u := by
      simpa [add_comm, add_left_comm, add_assoc, smul_add, smul_neg] using this
    have hne : g u ≠ 0 := hgu
    have hID : (g u)⁻¹ * g u = 1 := by
      simpa using inv_mul_cancel hne
    have := congrArg (fun x => (g u)⁻¹ • x) hsolve
    simpa [smul_smul, hID, one_smul, pow_two] using this

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
  ·
    -- plus side
    have := (grad_prod f (fun x => (g x)⁻¹) u hf hg_inv).1
    -- substitute ∇₊ of inverse from `hinv.1` and regroup scalars
    simpa [div_eq_mul_inv, smul_sub, smul_smul, star_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
      using this.trans (by
        simp [hinv.1, mul_comm, mul_left_comm, mul_assoc])
  ·
    -- minus side
    have := (grad_prod f (fun x => (g x)⁻¹) u hf hg_inv).2
    simpa [div_eq_mul_inv, smul_sub, smul_smul, pow_two, mul_comm, mul_left_comm, mul_assoc]
      using this.trans (by
        simp [hinv.2, mul_comm, mul_left_comm, mul_assoc])

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
  have h_Df_v : Df v = D₊ f u v + D₋ f u v := (R_split_point (H:=H) (W:=ℂ) f u v)
  have h_Df_Iv :
      Df (I • v) = I * D₊ f u v - I * D₋ f u v := by
    -- split at `I•v`, then commute/anticommute with `J`
    have := (R_split_point (H:=H) (W:=ℂ) f u (I • v))
    -- `D₊ (I•v) = I * D₊ v`,  `D₋ (I•v) = - I * D₋ v`
    simpa [Dplus_comm_J_point, Dminus_anticomm_J_point, Jc_apply, smul_eq_mul] using this
  -- Compute `D₊ (g ∘ f)` from the definition
  simp [DplusCLM, h_chain, ContinuousLinearMap.comp_apply, h_Dg,
        h_Df_v, h_Df_Iv, star_add, star_sub, star_smul, Complex.star_def, mul_comm, mul_left_comm,
        mul_assoc]

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
  have h_Df_v : Df v = D₊ f u v + D₋ f u v := (R_split_point (H:=H) (W:=ℂ) f u v)
  have h_Df_Iv :
      Df (I • v) = I * D₊ f u v - I * D₋ f u v := by
    have := (R_split_point (H:=H) (W:=ℂ) f u (I • v))
    simpa [Dplus_comm_J_point, Dminus_anticomm_J_point, Jc_apply, smul_eq_mul] using this
  simp [DminusCLM, h_chain, ContinuousLinearMap.comp_apply, h_Dg,
        h_Df_v, h_Df_Iv, star_add, star_sub, star_smul, Complex.star_def, mul_comm, mul_left_comm,
        mul_assoc]

end chain_rules

end scalar_rules
end Wirtinger
