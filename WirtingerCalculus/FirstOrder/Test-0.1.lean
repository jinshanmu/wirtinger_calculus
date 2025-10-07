import Mathlib
import WirtingerCalculus.Basic

/-!
First-order operation rules, star-based (no `Complex.conj`).

What this file provides:
* real-linear conjugation CLM `Cℂ : ℂ →L[ℝ] ℂ` defined via `star`
* `J` anti-commutes with `Cℂ`
* conjugation rules for `D₊`, `D₋` (both operator & directional forms)
* product / reciprocal / quotient rules (directional & gradient forms)
* formal partials on `ℂ` (`dz`, `dzbar`) and a 1D identity for `Df`
* directional chain rules for post-composition with a scalar map `g : ℂ → ℂ`

Only APIs used from your `Basic.lean`:
`Jc_apply`, `Jc_comp_Jc`, `R_split_point`, `Dplus_comm_J_point`,
`Dminus_anticomm_J_point`, `inner_gradPlus_eq_Dplus`,
`Dminus_eq_inner_gradMinus`, `fderivR_apply_split_grad`.
-/

noncomputable section
open scoped ComplexInnerProductSpace

namespace Wirtinger

local notation "D₊" => DplusCLM
local notation "D₋" => DminusCLM
local notation "∇₊" => gradPlus
local notation "∇₋" => gradMinus

/-! ## Conjugation over `ℂ` as a real-linear CLM, via `star` -/

/-- Real-linear “conjugation” on `ℂ`, implemented by `star`. -/
@[simp] def Cℂ : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := fun z => star z
  , map_add' := by
      intro x y; simpa using star_add x y
  , map_smul' := by
      intro r z
      -- goal over ℝ: star ((r : ℂ) * z) = (r : ℂ) * star z
      change star ((r : ℂ) * z) = (r : ℂ) * star z
      calc
        star ((r : ℂ) * z) = star z * (r : ℂ) := by
          simpa using (star_mul (r : ℂ) z)
        _ = (r : ℂ) * star z := by
          simpa [mul_comm] }
, cont := by
    -- let the `continuity` tactic solve continuity of `star`
    continuity }

@[simp] lemma Cℂ_apply (z : ℂ) : Cℂ z = star z := rfl

/-- `J` anti-commutes with conjugation (`star`) on `ℂ`. -/
lemma Jc_comp_Cℂ_anticom :
  (Jc ℂ).comp Cℂ = (-Cℂ).comp (Jc ℂ) := by
  ext z
  -- `star (I * z) = star z * star I`, then normalize with algebraic simp
  have h := star_mul (Complex.I) z
  simp [ContinuousLinearMap.comp_apply, Cℂ_apply, Jc_apply, h,
        mul_comm, mul_left_comm, mul_assoc]

/-! ## Scalar-valued rules on a complex Hilbert space -/

section scalar_rules
variables {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Conjugation (via `star`) -/

/-- Operator form: `D₊(star ∘ f) = Cℂ ∘L D₋ f`. -/
lemma Dplus_star_op (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) :
    D₊ (fun x => star (f x)) u = Cℂ ∘L D₋ f u := by
  classical
  have hDf :
      fderivR (H:=H) (W:=ℂ) (fun x => star (f x)) u
        = Cℂ ∘L fderivR (H:=H) (W:=ℂ) f u := by
    simpa [fderivR, ContinuousLinearMap.comp_apply]
      using ((Cℂ.hasFDerivAt (x := f u)).comp u hf.hasFDerivAt).fderiv
  ext v
  simp [DplusCLM, hDf, one_div, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_assoc, Jc_comp_Cℂ_anticom,
        sub_eq_add_neg]

/-- Operator form: `D₋(star ∘ f) = Cℂ ∘L D₊ f`. -/
lemma Dminus_star_op (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) :
    D₋ (fun x => star (f x)) u = Cℂ ∘L D₊ f u := by
  classical
  have hDf :
      fderivR (H:=H) (W:=ℂ) (fun x => star (f x)) u
        = Cℂ ∘L fderivR (H:=H) (W:=ℂ) f u := by
    simpa [fderivR, ContinuousLinearMap.comp_apply]
      using ((Cℂ.hasFDerivAt (x := f u)).comp u hf.hasFDerivAt).fderiv
  ext v
  simp [DminusCLM, hDf, one_div, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.comp_assoc, Jc_comp_Cℂ_anticom,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Directional forms. -/
@[simp] lemma Dplus_star_dir (f : H → ℂ) (u v : H) (hf : DifferentiableAt ℝ f u) :
  D₊ (fun x => star (f x)) u v = star (D₋ f u v) := by
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun (T : H →L[ℝ] ℂ) => T v) (Dplus_star_op (f:=f) (u:=u) hf)

@[simp] lemma Dminus_star_dir (f : H → ℂ) (u v : H) (hf : DifferentiableAt ℝ f u) :
  D₋ (fun x => star (f x)) u v = star (D₊ f u v) := by
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun (T : H →L[ℝ] ℂ) => T v) (Dminus_star_op (f:=f) (u:=u) hf)

/-! ### Product / reciprocal / quotient -/

section product_like
variable [CompleteSpace H]

/-- **Directional product rule** for `D₊`. -/
lemma Dplus_prod_dir (f g : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  D₊ (fun x => f x * g x) u v
    = D₊ f u v * g u + D₊ g u v * f u := by
  classical
  -- real product rule
  have hDf :
    fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u v
      = fderivR (H:=H) (W:=ℂ) f u v * g u
        + f u * fderivR (H:=H) (W:=ℂ) g u v := by
    simpa using
      congrArg (fun (T : H →L[ℝ] ℂ) => T v)
        ((hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv)
  have h1 : fderivR (H:=H) (W:=ℂ) f u v
            = D₊ f u v + D₋ f u v := by
    simpa using (R_split_point (H:=H) (W:=ℂ) (f:=f) (u:=u) (v:=v))
  have h2 : fderivR (H:=H) (W:=ℂ) g u v
            = D₊ g u v + D₋ g u v := by
    simpa using (R_split_point (H:=H) (W:=ℂ) (f:=g) (u:=u) (v:=v))
  -- compute `(J ∘ Df ∘ J) v`
  have hJf :
    (Jc ℂ) ((fderivR (H:=H) (W:=ℂ) f u) (J_H v))
      = - D₊ f u v + D₋ f u v := by
    have : (fderivR (H:=H) (W:=ℂ) f u) (J_H v)
            = D₊ f u (J_H v) + D₋ f u (J_H v) := by
      simpa using (R_split_point (H:=H) (W:=ℂ) (f:=f) (u:=u) (v:=J_H v))
    simp [Jc_apply, h1, this, Dplus_comm_J_point, Dminus_anticomm_J_point,
          Jc_comp_Jc, add_comm, add_left_comm, add_assoc, map_add, sub_eq_add_neg]
  have hJg :
    (Jc ℂ) ((fderivR (H:=H) (W:=ℂ) g u) (J_H v))
      = - D₊ g u v + D₋ g u v := by
    have : (fderivR (H:=H) (W:=ℂ) g u) (J_H v)
            = D₊ g u (J_H v) + D₋ g u (J_H v) := by
      simpa using (R_split_point (H:=H) (W:=ℂ) (f:=g) (u:=u) (v:=J_H v))
    simp [Jc_apply, h2, this, Dplus_comm_J_point, Dminus_anticomm_J_point,
          Jc_comp_Jc, add_comm, add_left_comm, add_assoc, map_add, sub_eq_add_neg]
  have hJ :
    (Jc ℂ) ((fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u) (J_H v))
      = (- D₊ f u v + D₋ f u v) * g u + f u * (- D₊ g u v + D₋ g u v) := by
    have hDfJ :
      (fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u) (J_H v)
        = (fderivR (H:=H) (W:=ℂ) f u) (J_H v) * g u
          + f u * (fderivR (H:=H) (W:=ℂ) g u) (J_H v) := by
      simpa using
        congrArg (fun (T : H →L[ℝ] ℂ) => T (J_H v))
          ((hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv)
    simp [hDfJ, hJf, hJg, Jc_apply, mul_add, add_mul,
          mul_comm, mul_left_comm, mul_assoc]
  -- put it in `D₊ = (Df - J∘Df∘J)/2`
  simp [DplusCLM, one_div, hDf, hJ, h1, h2,
        add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
        mul_comm, mul_left_comm, mul_assoc]

/-- **Directional product rule** for `D₋`. -/
lemma Dminus_prod_dir (f g : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  D₋ (fun x => f x * g x) u v
    = D₋ f u v * g u + D₋ g u v * f u := by
  classical
  -- same structure with `D₋`
  have hDf :
    fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u v
      = fderivR (H:=H) (W:=ℂ) f u v * g u
        + f u * fderivR (H:=H) (W:=ℂ) g u v := by
    simpa using
      congrArg (fun (T : H →L[ℝ] ℂ) => T v)
        ((hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv)
  have h1 : fderivR (H:=H) (W:=ℂ) f u v
            = D₊ f u v + D₋ f u v := by
    simpa using (R_split_point (H:=H) (W:=ℂ) (f:=f) (u:=u) (v:=v))
  have h2 : fderivR (H:=H) (W:=ℂ) g u v
            = D₊ g u v + D₋ g u v := by
    simpa using (R_split_point (H:=H) (W:=ℂ) (f:=g) (u:=u) (v:=v))
  have hJf :
    (Jc ℂ) ((fderivR (H:=H) (W:=ℂ) f u) (J_H v))
      = - D₊ f u v + D₋ f u v := by
    have : (fderivR (H:=H) (W:=ℂ) f u) (J_H v)
            = D₊ f u (J_H v) + D₋ f u (J_H v) := by
      simpa using (R_split_point (H:=H) (W:=ℂ) (f:=f) (u:=u) (v:=J_H v))
    simp [Jc_apply, h1, this, Dplus_comm_J_point, Dminus_anticomm_J_point,
          Jc_comp_Jc, add_comm, add_left_comm, add_assoc, map_add, sub_eq_add_neg]
  have hJg :
    (Jc ℂ) ((fderivR (H:=H) (W:=ℂ) g u) (J_H v))
      = - D₊ g u v + D₋ g u v := by
    have : (fderivR (H:=H) (W:=ℂ) g u) (J_H v)
            = D₊ g u (J_H v) + D₋ g u (J_H v) := by
      simpa using (R_split_point (H:=H) (W:=ℂ) (f:=g) (u:=u) (v:=J_H v))
    simp [Jc_apply, h2, this, Dplus_comm_J_point, Dminus_anticomm_J_point,
          Jc_comp_Jc, add_comm, add_left_comm, add_assoc, map_add, sub_eq_add_neg]
  have hJ :
    (Jc ℂ) ((fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u) (J_H v))
      = (- D₊ f u v + D₋ f u v) * g u + f u * (- D₊ g u v + D₋ g u v) := by
    have hDfJ :
      (fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u) (J_H v)
        = (fderivR (H:=H) (W:=ℂ) f u) (J_H v) * g u
          + f u * (fderivR (H:=H) (W:=ℂ) g u) (J_H v) := by
      simpa using
        congrArg (fun (T : H →L[ℝ] ℂ) => T (J_H v))
          ((hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv)
    simp [hDfJ, hJf, hJg, Jc_apply, mul_add, add_mul,
          mul_comm, mul_left_comm, mul_assoc]
  simp [DminusCLM, one_div, hDf, hJ, h1, h2,
        add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
        mul_comm, mul_left_comm, mul_assoc]

/-- **Gradient product rule.** -/
lemma grad_prod (f g : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  ∇₊ (fun x => f x * g x) u
    = star (g u) • ∇₊ f u + star (f u) • ∇₊ g u
∧ ∇₋ (fun x => f x * g x) u
    = (g u) • ∇₋ f u + (f u) • ∇₋ g u := by
  classical
  constructor
  ·
    have hv : ∀ v : H,
      ⟪ ∇₊ (fun x => f x * g x) u
        - (star (g u) • ∇₊ f u + star (f u) • ∇₊ g u), v ⟫_ℂ = 0 := by
      intro v
      have := Dplus_prod_dir (f:=f) (g:=g) (u:=u) (v:=v) hf hg
      simpa [inner_sub_left, inner_add_left, inner_smul_left,
             inner_gradPlus_eq_Dplus, star_mul, mul_comm, mul_left_comm, mul_assoc]
        using this
    have h0 := hv (∇₊ (fun x => f x * g x) u
                   - (star (g u) • ∇₊ f u + star (f u) • ∇₊ g u))
    have : (∇₊ (fun x => f x * g x) u
             - (star (g u) • ∇₊ f u + star (f u) • ∇₊ g u)) = 0 := by
      simpa using (inner_self_eq_zero.mp h0)
    simpa using sub_eq_zero.mp this
  ·
    have hv : ∀ v : H,
      ⟪ v, ∇₋ (fun x => f x * g x) u
           - ((g u) • ∇₋ f u + (f u) • ∇₋ g u) ⟫_ℂ = 0 := by
      intro v
      have := Dminus_prod_dir (f:=f) (g:=g) (u:=u) (v:=v) hf hg
      simpa [sub_eq_add_neg, inner_add_right, inner_smul_right,
             Dminus_eq_inner_gradMinus, mul_comm, mul_left_comm, mul_assoc]
        using this
    have h0 := hv (∇₋ (fun x => f x * g x) u
                   - ((g u) • ∇₋ f u + (f u) • ∇₋ g u))
    have : (∇₋ (fun x => f x * g x) u
             - ((g u) • ∇₋ f u + (f u) • ∇₋ g u)) = 0 := by
      simpa using (inner_self_eq_zero.mp h0)
    simpa using sub_eq_zero.mp this

/-- **Reciprocal rule** (pointwise nonvanishing). -/
lemma grad_inv (g : H → ℂ) (u : H)
    (hg : DifferentiableAt ℝ g u) (hgu : g u ≠ 0) :
  ∇₊ (fun x => (g x)⁻¹) u = - ((star (g u)) ^ (2 : ℕ))⁻¹ • ∇₊ g u
∧ ∇₋ (fun x => (g x)⁻¹) u = - ((g u) ^ (2 : ℕ))⁻¹ • ∇₋ g u := by
  classical
  have hconst₊ : ∇₊ (fun _ : H => (1 : ℂ)) u = 0 := by simpa
  have hconst₋ : ∇₋ (fun _ : H => (1 : ℂ)) u = 0 := by simpa
  have hprod := grad_prod (f:=g) (g:=fun x => (g x)⁻¹) (u:=u) hg (hg.inv hgu)
  constructor
  ·
    -- 0 = star (g⁻¹) • ∇₊ g + star g • ∇₊ (g⁻¹)
    have := hprod.1
    -- Solve for ∇₊ (g⁻¹)
    have : star (g u) • ∇₊ (fun x => (g x)⁻¹) u
            = - star ((g u)⁻¹) • ∇₊ g u := by
      -- move `hconst₊` to the left, then rearrange
      simpa [hconst₊, smul_add, add_comm, add_left_comm, add_assoc,
             mul_smul, smul_add, sub_eq_add_neg] using this
    -- multiply both sides by (star g)⁻¹
    have := congrArg (fun x => (star (g u))⁻¹ • x) this
    -- star ((g u)⁻¹) = (star (g u))⁻¹, so product is (star g)⁻²
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc,
           pow_two] using this
  ·
    -- 0 = (g) • ∇₋ (g⁻¹) + (g⁻¹) • ∇₋ g
    have := hprod.2
    have : (g u) • ∇₋ (fun x => (g x)⁻¹) u
            = - (g u)⁻¹ • ∇₋ g u := by
      simpa [hconst₋, smul_add, add_comm, add_left_comm, add_assoc,
             mul_smul, smul_add, sub_eq_add_neg] using this
    have := congrArg (fun x => (g u)⁻¹ • x) this
    simpa [smul_smul, pow_two, mul_comm, mul_left_comm, mul_assoc] using this

/-- **Quotient rule** (pointwise nonvanishing). -/
lemma grad_quot (f g : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) (hgu : g u ≠ 0) :
  ∇₊ (fun x => f x / g x) u
    = ((star (g u)) ^ (2 : ℕ))⁻¹ • (star (g u) • ∇₊ f u - star (f u) • ∇₊ g u)
∧ ∇₋ (fun x => f x / g x) u
    = ((g u) ^ (2 : ℕ))⁻¹ • ((g u) • ∇₋ f u - (f u) • ∇₋ g u) := by
  classical
  have hinv := grad_inv (g:=g) (u:=u) (hg:=hg) (hgu:=hgu)
  constructor
  ·
    have := (grad_prod (f:=f) (g:=fun x => (g x)⁻¹) (u:=u) hf (hg.inv hgu)).1
    simpa [mul_comm, mul_left_comm, mul_assoc, smul_sub, mul_smul,
           hinv.1] using this
  ·
    have := (grad_prod (f:=f) (g:=fun x => (g x)⁻¹) (u:=u) hf (hg.inv hgu)).2
    simpa [mul_comm, mul_left_comm, mul_assoc, smul_sub, mul_smul,
           hinv.2] using this

end product_like

/-! ## Formal Wirtinger partials on `ℂ` -/

section partials_on_C
variable [CompleteSpace ℂ]

/-- `dz f z := D₊ f z 1`. -/
def dz (f : ℂ → ℂ) (z : ℂ) : ℂ := D₊ (H:=ℂ) (W:=ℂ) f z (1 : ℂ)

/-- `dzbar f z := D₋ f z 1`. -/
def dzbar (f : ℂ → ℂ) (z : ℂ) : ℂ := D₋ (H:=ℂ) (W:=ℂ) f z (1 : ℂ)

/-- Relations between gradients and formal partials on `ℂ`. -/
lemma grads_vs_partials (f : ℂ → ℂ) (z : ℂ) :
  (∇₊ f z = dz f z) ∧ (dzbar f z = star (∇₋ f z)) := by
  constructor
  ·
    -- `dz = D₊ f z 1 = ⟪∇₊,1⟫ = ∇₊`
    have := (inner_gradPlus_eq_Dplus (H:=ℂ) (f:=f) (u:=z) (v:=(1:ℂ)))
    simpa [dz] using this.symm
  ·
    -- `dzbar = D₋ f z 1 = ⟪1, ∇₋⟫ = star (∇₋)`
    have := (Dminus_eq_inner_gradMinus (H:=ℂ) (f:=f) (u:=z) (v:=(1:ℂ)))
    simpa [dzbar] using this

/-- 1D identity on `ℂ`:
`Df[u] w = (dz f u) * star w + w * (dzbar f u)`. -/
lemma fderiv_via_partials (f : ℂ → ℂ) (u w : ℂ) :
  fderivR (H:=ℂ) (W:=ℂ) f u w
    = (dz f u) * star w + w * (dzbar f u) := by
  have := fderivR_apply_split_grad (H:=ℂ) (f:=f) (u:=u) (v:=w)
  rcases (grads_vs_partials (f:=f) (z:=u)) with ⟨h₊, h₋⟩
  simpa [h₊, h₋, star_mul] using this

end partials_on_C

/-! ## Chain rules (directional) for post-composition by `g : ℂ → ℂ` -/

section chain_rules
variables [CompleteSpace H]

/-- Directional chain rule for `D₊` when postcomposing with `g : ℂ → ℂ`. -/
lemma Dplus_comp_scalar_dir
  (f : H → ℂ) (g : ℂ → ℂ) (u : H) (v : H)
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g (f u)) :
  D₊ (fun x => g (f x)) u v
    = (dz g (f u)) * D₊ f u v + (dzbar g (f u)) * D₋ f u v := by
  classical
  -- ℝ-chain rule
  have hDf : fderivR (H:=H) (W:=ℂ) (fun x => g (f x)) u
              = (fderivR (H:=ℂ) (W:=ℂ) g (f u)).comp (fderivR f u) := by
    simpa [fderivR] using (hg.hasFDerivAt.comp u hf.hasFDerivAt).fderiv
  -- split the ℂ→ℂ derivative via partials
  have hs : ∀ w, fderivR (H:=ℂ) (W:=ℂ) g (f u) w
                = (dz g (f u)) * star w + w * (dzbar g (f u)) := by
    intro w; simpa using (fderiv_via_partials (f:=g) (u:=f u) (w:=w))
  -- split `fderivR f u`
  have hsplit_f : ∀ w, fderivR (H:=H) (W:=ℂ) f u w
                = D₊ f u w + D₋ f u w := by
    intro w; simpa using (R_split_point (H:=H) (W:=ℂ) (f:=f) (u:=u) (v:=w))
  -- compute by definition of D₊
  simp [DplusCLM, one_div, hDf, ContinuousLinearMap.comp_apply,
       ContinuousLinearMap.comp_assoc, sub_eq_add_neg,
       hs (fderivR f u v), hsplit_f v,
       Jc_apply, Dplus_comm_J_point, Dminus_anticomm_J_point,
       add_comm, add_left_comm, add_assoc, map_add, mul_add, add_mul]

/-- Directional chain rule for `D₋` when postcomposing with `g : ℂ → ℂ`. -/
lemma Dminus_comp_scalar_dir
  (f : H → ℂ) (g : ℂ → ℂ) (u : H) (v : H)
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g (f u)) :
  D₋ (fun x => g (f x)) u v
    = (dzbar g (f u)) * D₊ f u v + (dz g (f u)) * D₋ f u v := by
  classical
  have hDf : fderivR (H:=H) (W:=ℂ) (fun x => g (f x)) u
              = (fderivR (H:=ℂ) (W:=ℂ) g (f u)).comp (fderivR f u) := by
    simpa [fderivR] using (hg.hasFDerivAt.comp u hf.hasFDerivAt).fderiv
  have hs : ∀ w, fderivR (H:=ℂ) (W:=ℂ) g (f u) w
                = (dz g (f u)) * star w + w * (dzbar g (f u)) := by
    intro w; simpa using (fderiv_via_partials (f:=g) (u:=f u) (w:=w))
  have hsplit_f : ∀ w, fderivR (H:=H) (W:=ℂ) f u w
                = D₊ f u w + D₋ f u w := by
    intro w; simpa using (R_split_point (H:=H) (W:=ℂ) (f:=f) (u:=u) (v:=w))
  simp [DminusCLM, one_div, hDf, ContinuousLinearMap.comp_apply,
       ContinuousLinearMap.comp_assoc, sub_eq_add_neg,
       hs (fderivR f u v), hsplit_f v,
       Jc_apply, Dplus_comm_J_point, Dminus_anticomm_J_point,
       add_comm, add_left_comm, add_assoc, map_add, mul_add, add_mul]

end chain_rules

end scalar_rules
end Wirtinger
