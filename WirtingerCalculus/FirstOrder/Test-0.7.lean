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

Only APIs used from `Basic.lean`:
`Jc_apply`, `Jc_comp_Jc`, `R_split_point`, `Dplus_comm_J_point`,
`Dminus_anticomm_J_point`, `inner_gradPlus_eq_Dplus`,
`Dminus_eq_inner_gradMinus`, `Aℒ_apply`.
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

/-! ## Tiny star-toolkit on `ℂ` -/

-- Keep `Complex.star_def` out of simp to avoid re/im explosions.
attribute [-simp] Complex.star_def

-- Use generic `star_*` lemmas (works in all Mathlib versions).
@[simp] lemma star_add' (x y : ℂ) : star (x + y) = star x + star y := by
  simpa using (star_add (x) (y))
@[simp] lemma star_mul' (x y : ℂ) : star (x * y) = star y * star x := by
  simpa using (star_mul (x) (y))
@[simp] lemma star_ofReal' (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
  simpa using Complex.conj_ofReal r
@[simp] lemma Complex.star_I : star (I : ℂ) = -I := by
  simpa using Complex.conj_I

-- Tiny algebra: move `I` through products in `ℂ`.
@[simp] lemma I_mul_move (a b : ℂ) : I * (a * b) = a * (I * b) := by
  calc
    I * (a * b) = (I * a) * b := by simpa [mul_assoc]
    _           = (a * I) * b := by simpa [mul_comm]
    _           = a * (I * b) := by simpa [mul_assoc]

/-! ## Conjugation over `ℂ` as a real-linear CLM, via `star` -/

/-- Real-linear complex conjugation on `ℂ`, implemented by `star`. -/
def Cℂ : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := fun z => star z
  , map_add' := by intro x y; simpa using (star_add' x y)
  , map_smul' := by
      intro r z
      change star ((r : ℂ) * z) = (r : ℂ) * star z
      simpa [star_mul', star_ofReal', mul_comm] }
, cont := continuous_star }

@[simp] lemma Cℂ_apply (z : ℂ) : Cℂ z = star z := rfl

/-- `J` anti-commutes with real-linear conjugation on `ℂ`. -/
lemma Jc_comp_Cℂ_anticom :
  (Jc ℂ).comp Cℂ = - (Cℂ.comp (Jc ℂ)) := by
  ext z
  simp [Jc_apply, Cℂ_apply, star_mul', Complex.star_I, mul_comm, mul_left_comm, mul_assoc]

/-- Compatibility of the anti-twist with conjugation. -/
lemma Aℒ_comp_Cℂ
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  (T : H →L[ℝ] ℂ) :
  Aℒ (H:=H) (W:=ℂ) (Cℂ.comp T) = - Cℂ.comp (Aℒ (H:=H) (W:=ℂ) T) := by
  ext v
  simp [Aℒ_apply, Cℂ_apply, ContinuousLinearMap.comp_apply, star_mul', Complex.star_I,
        mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]

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
  simp [DplusCLM, DminusCLM, hDf, Aℒ_comp_Cℂ, sub_eq_add_neg,
        ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]

/-- Operator form: `D₋(star ∘ f) = Cℂ ∘L D₊ f`. -/
lemma Dminus_star_op (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) :
    D₋ (fun x => star (f x)) u = Cℂ.comp (D₊ f u) := by
  classical
  let D := fderivR f u
  have hDf : fderivR (fun x => star (f x)) u = Cℂ.comp D :=
    (Cℂ.hasFDerivAt.comp u hf.hasFDerivAt).fderiv
  simp [DminusCLM, DplusCLM, hDf, Aℒ_comp_Cℂ,
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
    = f u * D₊ g u v + g u * D₊ f u v := by
  classical
  let Df := fderivR f u
  let Dg := fderivR g u
  have h_mul : fderivR (fun x => f x * g x) u = f u • Dg + g u • Df :=
    fderiv_mul hf hg
  have hA :
      Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)
        = f u • Aℒ (H:=H) (W:=ℂ) Dg + g u • Aℒ (H:=H) (W:=ℂ) Df := by
    ext w; simp [Aℒ_apply, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc]
  have : D₊ (fun x => f x * g x) u
        = f u • D₊ g u + g u • D₊ f u := by
    ext w
    simp [DplusCLM, h_mul, hA, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul,
          sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc, I_mul_move]
  simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] using
    congrArg (fun L => L v) this

/-- **Directional product rule** for `D₋`. -/
lemma Dminus_prod_dir (f g : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  D₋ (fun x => f x * g x) u v
    = f u * D₋ g u v + g u * D₋ f u v := by
  classical
  let Df := fderivR f u
  let Dg := fderivR g u
  have h_mul : fderivR (fun x => f x * g x) u = f u • Dg + g u • Df :=
    fderiv_mul hf hg
  have hA :
      Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)
        = f u • Aℒ (H:=H) (W:=ℂ) Dg + g u • Aℒ (H:=H) (W:=ℂ) Df := by
    ext w; simp [Aℒ_apply, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc]
  have : D₋ (fun x => f x * g x) u
        = f u • D₋ g u + g u • D₋ f u := by
    ext w
    simp [DminusCLM, h_mul, hA, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul,
          add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc, I_mul_move]
  simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] using
    congrArg (fun L => L v) this

/-- **Gradient product rule.** -/
lemma grad_prod (f g : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  ∇₊ (fun x => f x * g x) u
    = star (g u) • ∇₊ f u + star (f u) • ∇₊ g u
∧ ∇₋ (fun x => f x * g x) u
    = g u • ∇₋ f u + f u • ∇₋ g u := by
  constructor
  · -- use Riesz: inject through `toDual`
    apply (InnerProductSpace.toDual ℂ H).injective
    ext v
    simp [inner_gradPlus_eq_Dplus, Dplus_prod_dir f g u v hf hg,
          inner_add_left, inner_smul_left, star_star]
  · apply (InnerProductSpace.toDual ℂ H).injective
    ext v
    simp [Dminus_eq_inner_gradMinus, Dminus_prod_dir f g u v hf hg,
          inner_add_right, inner_smul_right]

end product_like

/-!  Congruence under `=ᶠ[𝓝 u]`. -/
section congr_helpers

lemma fderivR_congr_of_eventuallyEq
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  fderivR f u = fderivR g u := by
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
  simp [DplusCLM, fderivR_congr_of_eventuallyEq (H:=H) hf hg h]

lemma DminusCLM_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  D₋ f u = D₋ g u := by
  simp [DminusCLM, fderivR_congr_of_eventuallyEq (H:=H) hf hg h]

-- gradient congruences via the inner-product injection
lemma gradPlus_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  ∇₊ f u = ∇₊ g u := by
  have hD := DplusCLM_congr_of_eventuallyEq (H:=H) hf hg h
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v; simpa [inner_gradPlus_eq_Dplus] using congrArg (fun L => L v) hD

lemma gradMinus_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  ∇₋ f u = ∇₋ g u := by
  have hD := DminusCLM_congr_of_eventuallyEq (H:=H) hf hg h
  apply (InnerProductSpace.toDual ℂ H).injective
  ext v; simpa [Dminus_eq_inner_gradMinus] using congrArg (fun L => L v) hD

end congr_helpers

/-! ## Formal Wirtinger partials on `ℂ` -/

section partials_on_C
variable [CompleteSpace ℂ]

/-- `dz f z := D₊ f z 1`. -/
def dz (f : ℂ → ℂ) (z : ℂ) : ℂ := D₊ f z (1 : ℂ)

/-- `dzbar f z := D₋ f z 1`. -/
def dzbar (f : ℂ → ℂ) (z : ℂ) : ℂ := D₋ f z (1 : ℂ)

/-- 1D identity on `ℂ`: `fderivR f u w = dz f u * w + dzbar f u * star w`. -/
lemma fderiv_via_partials (f : ℂ → ℂ) (u w : ℂ) :
  fderivR f u w = dz f u * w + dzbar f u * star w := by
  classical
  set D := fderivR f u
  have h1 : D 1 = dz f u + dzbar f u := by
    simpa [dz, dzbar] using
      (show D 1 = D₊ f u 1 + D₋ f u 1 from R_split_point (f:=f) (u:=u) (v:=1))
  have hI : D I = I * dz f u - I * dzbar f u := by
    have hplus : D₊ f u (I • (1:ℂ)) = I * D₊ f u 1 := by
      simpa [Jc_apply, smul_eq_mul] using (Dplus_comm_J_point (f:=f) (u:=u) (v:=1))
    have hminus : D₋ f u (I • (1:ℂ)) = - I * D₋ f u 1 := by
      simpa [Jc_apply, smul_eq_mul] using (Dminus_anticomm_J_point (f:=f) (u:=u) (v:=1))
    have : D I = D₊ f u I + D₋ f u I := R_split_point (f:=f) (u:=u) (v:=I)
    simpa [dz, dzbar, smul_eq_mul, sub_eq_add_neg] using
      this.trans (by simpa [smul_eq_mul] using congrArg₂ HAdd.hAdd hplus hminus)
  have hw : w = w.re • (1 : ℂ) + w.im • I := by
    simpa [smul_eq_mul] using (re_add_im w)
  calc
    D w
        = D (w.re • (1 : ℂ) + w.im • I) := by simpa [hw]
    _   = (w.re : ℝ) • D 1 + (w.im : ℝ) • D I := by
          simpa [map_add]  -- `map_smul` is a simp lemma for CLMs over ℝ
    _   = (w.re : ℂ) * (dz f u + dzbar f u)
          + (w.im : ℂ) * (I * dz f u - I * dzbar f u) := by
          simpa [smul_eq_mul, h1, hI]
    _   = dz f u * w + dzbar f u * star w := by
      -- compute `star w` and do a quick rearrangement
      have hstar : star w = (w.re : ℂ) - (w.im : ℂ) * I := by
        have := congrArg star (re_add_im w)
        simpa [star_add', star_mul', star_ofReal', Complex.star_I,
               sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using this
      have hw' : w = (w.re : ℂ) + (w.im : ℂ) * I := by simpa using (re_add_im w)
      simpa [hw', hstar, mul_comm, mul_left_comm, mul_assoc,
             add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

end partials_on_C

/-! ## Quotient / inverse via gradients -/

section reciprocal_quotient
variable [CompleteSpace H]

/-- **Reciprocal rule** (pointwise nonvanishing). -/
lemma grad_inv (g : H → ℂ) (u : H)
    (hg : DifferentiableAt ℝ g u) (hgu : g u ≠ 0) :
  ∇₊ (fun x => (g x)⁻¹) u = - ((star (g u)) ^ 2)⁻¹ • ∇₊ g u
∧ ∇₋ (fun x => (g x)⁻¹) u = - ((g u) ^ 2)⁻¹ • ∇₋ g u := by
  classical
  have hg_inv : DifferentiableAt ℝ (fun x => (g x)⁻¹) u := hg.inv hgu
  have hprod := grad_prod g (fun x => (g x)⁻¹) u hg hg_inv
  have h_eventually_one :
    (fun x => g x * (g x)⁻¹) =ᶠ[𝓝 u] (fun _ => (1 : ℂ)) := by
    filter_upwards [hg.continuousAt.eventually_ne hgu] with x hx
    simp [hx]
  -- gradients of constant = 0, then isolate
  have h_left_plus :
      ∇₊ (fun x => g x * (g x)⁻¹) u = 0 := by
    have := gradPlus_congr_of_eventuallyEq (H:=H)
        (hg.mul hg_inv) (differentiableAt_const _) h_eventually_one
    simpa using this
  have h_left_minus :
      ∇₋ (fun x => g x * (g x)⁻¹) u = 0 := by
    have := gradMinus_congr_of_eventuallyEq (H:=H)
        (hg.mul hg_inv) (differentiableAt_const _) h_eventually_one
    simpa using this
  constructor
  · have : 0
        = star ((g u)⁻¹) • ∇₊ g u
          + star (g u) • ∇₊ (fun x => (g x)⁻¹) u := by
      simpa [h_left_plus] using hprod.1
    have hsolve :
        star (g u) • ∇₊ (fun x => (g x)⁻¹) u
          = - star ((g u)⁻¹) • ∇₊ g u := by
      simpa [add_eq_zero_iff_eq_neg] using this
    have hne : star (g u) ≠ 0 := star_ne_zero.mpr hgu
    simpa [smul_smul, inv_smul_smul₀ hne, one_smul, star_inv, pow_two] using
      congrArg (fun x => (star (g u))⁻¹ • x) hsolve
  · have : 0
        = (g u)⁻¹ • ∇₋ g u
          + g u • ∇₋ (fun x => (g x)⁻¹) u := by
      simpa [h_left_minus] using hprod.2
    have hsolve :
        g u • ∇₋ (fun x => (g x)⁻¹) u
          = - (g u)⁻¹ • ∇₋ g u := by
      simpa [add_eq_zero_iff_eq_neg] using this
    simpa [smul_smul, inv_smul_smul₀ hgu, one_smul, pow_two] using
      congrArg (fun x => (g u)⁻¹ • x) hsolve

/-- **Quotient rule** (pointwise nonvanishing). -/
lemma grad_quot (f g : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (hgu : g u ≠ 0) :
  ∇₊ (fun x => f x / g x) u
    = ((star (g u)) ^ 2)⁻¹ • (star (g u) • ∇₊ f u - star (f u) • ∇₊ g u)
∧ ∇₋ (fun x => f x / g x) u
    = ((g u) ^ 2)⁻¹ • (g u • ∇₋ f u - f u • ∇₋ g u) := by
  classical
  have hg_inv : DifferentiableAt ℝ (fun x => (g x)⁻¹) u := hg.inv hgu
  have hinv := grad_inv (H:=H) g u hg hgu
  constructor
  · -- plus side
    have h_prod := (grad_prod f (fun x => (g x)⁻¹) u hf hg_inv).1
    -- rewrite `/` to `* (·)⁻¹` and substitute `hinv.1`
    have := h_prod
    --   ∇₊(f * g⁻¹) = (star g)⁻¹•∇₊f + star f • (-(star g)^(-2)•∇₊g)
    have h' : ∇₊ (fun x => f x * (g x)⁻¹) u
        = (star (g u))⁻¹ • ∇₊ f u
          + star (f u) • (-(star (g u) ^ 2)⁻¹ • ∇₊ g u) := by
      simpa [star_inv, pow_two] using
        (show _ = (star ((g u)⁻¹)) • ∇₊ f u + star (f u) • (hinv.1)
          from rfl)
    -- massage to target
    simpa [div_eq_mul_inv, smul_add, smul_smul, star_inv, pow_two, sub_eq_add_neg,
           mul_comm, mul_left_comm, mul_assoc] using
      h'.trans rfl
  · -- minus side
    have h_prod := (grad_prod f (fun x => (g x)⁻¹) u hf hg_inv).2
    have h' : ∇₋ (fun x => f x * (g x)⁻¹) u
        = (g u)⁻¹ • ∇₋ f u + f u • (-(g u ^ 2)⁻¹ • ∇₋ g u) := by
      simpa [pow_two] using
        (show _ = ((g u)⁻¹) • ∇₋ f u + f u • (hinv.2) from rfl)
    simpa [div_eq_mul_inv, smul_add, smul_smul, pow_two, sub_eq_add_neg,
           mul_comm, mul_left_comm, mul_assoc] using h'.trans rfl

end reciprocal_quotient

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
  have h_Dg (w : ℂ) : Dg w = dz g (f u) * w + dzbar g (f u) * star w :=
    fderiv_via_partials g (f u) w
  have h_Df_v : Df v = D₊ f u v + D₋ f u v := by
    simpa using (R_split_point (f:=f) (u:=u) (v:=v))
  have h_Df_Iv :
      Df (I • v) = I * D₊ f u v - I * D₋ f u v := by
    -- split at `I•v` then use comm/anticomm
    have := R_split_point (f:=f) (u:=u) (v:=I • v)
    simpa [Jc_apply, smul_eq_mul, sub_eq_add_neg] using this
  simp [DplusCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, Aℒ_apply,
        ContinuousLinearMap.comp_apply, h_chain, h_Dg, h_Df_v, h_Df_Iv, smul_eq_mul,
        star_add', star_mul', Complex.star_I, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, I_mul_move]

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
  have h_Df_v : Df v = D₊ f u v + D₋ f u v := by
    simpa using (R_split_point (f:=f) (u:=u) (v:=v))
  have h_Df_Iv :
      Df (I • v) = I * D₊ f u v - I * D₋ f u v := by
    have := R_split_point (f:=f) (u:=u) (v:=I • v)
    simpa [Jc_apply, smul_eq_mul, sub_eq_add_neg] using this
  simp [DminusCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, Aℒ_apply,
        ContinuousLinearMap.comp_apply, h_chain, h_Dg, h_Df_v, h_Df_Iv, smul_eq_mul,
        star_add', star_mul', Complex.star_I, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, I_mul_move]

end chain_rules

end scalar_rules
end Wirtinger
