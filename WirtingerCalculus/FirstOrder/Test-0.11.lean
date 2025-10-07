import Mathlib
import WirtingerCalculus.Basic

/-!
First-order rules for scalar-valued maps over complex inner-product spaces.

What this file provides (kept lean to avoid `simp` loops / heartbeats):
* `Cℂ : ℂ →L[ℝ] ℂ` — real-linear complex conjugation (implemented by `star`)
* `Jc` anti-commutes with `Cℂ` on `ℂ`
* `Aℒ` compatibility with conjugation: `Aℒ (Cℂ ∘ T) = - (Cℂ ∘ Aℒ T)`
* Conjugation rules for Wirtinger derivatives:
    - `D₊(star ∘ f) u v = star (D₋ f u v)`
    - `D₋(star ∘ f) u v = star (D₊ f u v)`
  (and operator forms by `ext`).
* Product rules (directional):
    - `D₊(f*g) u v = f u * D₊ g u v + g u * D₊ f u v`
    - `D₋(f*g) u v = f u * D₋ g u v + g u * D₋ f u v`
* Congruence under `=ᶠ[𝓝 u]` for `D₊` and `D₋`.
* A small algebra toolkit on `ℂ` to make simp robust.
* Minimal definitions `dz`, `dzbar` on `ℂ`.
-/

noncomputable section
open Complex
open scoped ComplexInnerProductSpace Topology

namespace Wirtinger

-- Handy notations
local notation "D₊" => DplusCLM
local notation "D₋" => DminusCLM

/-! ## Small algebra toolkit on `ℂ` (non-recursive simp helpers) -/

@[simp] lemma star_add' (x y : ℂ) : star (x + y) = star x + star y := by
  simp

@[simp] lemma star_mul' (x y : ℂ) : star (x * y) = star x * star y := by
  simp

@[simp] lemma ofReal_mul_I (r : ℝ) : (r : ℂ) * I = I * (r : ℂ) := by
  simp [mul_comm]

@[simp] lemma smul_one_real (r : ℝ) : r • (1 : ℂ) = (r : ℂ) := by
  simp

@[simp] lemma smul_I_real (r : ℝ) : r • (I : ℂ) = (r : ℂ) * I := by
  simp

/-! ## Real-linear conjugation on `ℂ` -/

/-- Real-linear complex conjugation on `ℂ` as a continuous linear map. -/
def Cℂ : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := star
  , map_add' := by
      intro x y; simp
  , map_smul' := by
      intro r z
      -- Over ℝ, `r • z = (r : ℂ) * z` and `star` preserves real scalars and is multiplicative.
      simp },
  cont := continuous_star }

@[simp] lemma Cℂ_apply (z : ℂ) : Cℂ z = star z := rfl

/-- `J` anti-commutes with real-linear conjugation on `ℂ`. -/
lemma Jc_comp_Cℂ_anticom :
  (Jc ℂ).comp Cℂ = - (Cℂ.comp (Jc ℂ)) := by
  ext z
  have hI : star (I : ℂ) = -I := by simp
  -- LHS = I * star z; RHS = -(star (I * z)) = - (star I * star z) = I * star z.
  simp [ContinuousLinearMap.comp_apply, Jc_apply, Cℂ_apply, hI, mul_comm, mul_left_comm, mul_assoc]

/-! ## Compatibility of `Aℒ` with conjugation -/

section Aℒ_conj
variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Compatibility of the anti-twist with conjugation. -/
lemma Aℒ_comp_Cℂ (T : H →L[ℝ] ℂ) :
  Aℒ (H:=H) (W:=ℂ) (Cℂ.comp T) = - Cℂ.comp (Aℒ (H:=H) (W:=ℂ) T) := by
  -- Expand the (sandwich) definition of `Aℒ` and use anticommutation above.
  ext v
  have hI : star (I : ℂ) = -I := by simp
  simp [ContinuousLinearMap.comp_apply, Cℂ_apply, hI, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
end Aℒ_conj

/-! ## A basic congruence lemma for `fderivR` (needed later) -/

-- congruence of `fderivR` under eventual equality
lemma fderivR_congr_of_eventuallyEq
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  fderivR f u = fderivR g u := by
  have hf' := hf.hasFDerivAt
  have hg' := hg.hasFDerivAt
  have : HasFDerivAt g (fderivR f u) u := hf'.congr_of_eventuallyEq h.symm
  exact hg'.unique this

/-! ## Scalar-valued rules on a complex Hilbert space -/

section scalar_rules
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Conjugation (via `star`) -/

lemma Dplus_star_dir (f : H → ℂ) (u v : H) (hf : DifferentiableAt ℝ f u) :
  D₊ (fun x => star (f x)) u v = star (D₋ f u v) := by
  classical
  set T := fderivR f u
  -- `fderivR (star ∘ f) = Cℂ ∘ T`
  have hDf :
      fderivR (fun x => star (f x)) u = (Cℂ : ℂ →L[ℝ] ℂ).comp T :=
    ((Cℂ : ℂ →L[ℝ] ℂ).hasFDerivAt.comp u hf.hasFDerivAt).fderiv
  -- `Aℒ` compat with `Cℂ`
  have hA : Aℒ (H:=H) (W:=ℂ) ((Cℂ : ℂ →L[ℝ] ℂ).comp T)
            = - (Cℂ : ℂ →L[ℝ] ℂ).comp (Aℒ (H:=H) (W:=ℂ) T) :=
    Aℒ_comp_Cℂ (H:=H) (T := T)
  -- Expand definitions with light `simp`.
  have : D₊ (fun x => star (f x)) u v
        = (1/2 : ℝ) • ((Cℂ (T v)) + Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
    simp (only) [DplusCLM, hDf, hA, ContinuousLinearMap.comp_apply, sub_eq_add_neg,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_add]
  -- Use ℝ-linearity of `Cℂ`.
  have : D₊ (fun x => star (f x)) u v
        = Cℂ ((1/2 : ℝ) • (T v + (Aℒ (H:=H) (W:=ℂ) T) v)) := by
    simpa [map_add, map_smul] using this
  -- Recognize `D₋ f u v`.
  simpa [DminusCLM, Cℂ_apply, sub_eq_add_neg, ContinuousLinearMap.add_apply,
         ContinuousLinearMap.smul_apply, smul_add] using this

lemma Dminus_star_dir (f : H → ℂ) (u v : H) (hf : DifferentiableAt ℝ f u) :
  D₋ (fun x => star (f x)) u v = star (D₊ f u v) := by
  classical
  set T := fderivR f u
  have hDf :
      fderivR (fun x => star (f x)) u = (Cℂ : ℂ →L[ℝ] ℂ).comp T :=
    ((Cℂ : ℂ →L[ℝ] ℂ).hasFDerivAt.comp u hf.hasFDerivAt).fderiv
  have hA : Aℒ (H:=H) (W:=ℂ) ((Cℂ : ℂ →L[ℝ] ℂ).comp T)
            = - (Cℂ : ℂ →L[ℝ] ℂ).comp (Aℒ (H:=H) (W:=ℂ) T) :=
    Aℒ_comp_Cℂ (H:=H) (T := T)
  have : D₋ (fun x => star (f x)) u v
        = (1/2 : ℝ) • ((Cℂ (T v)) - Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
    simp (only) [DminusCLM, hDf, hA, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, add_comm,
      add_left_comm, add_assoc, smul_sub, sub_eq_add_neg]
  have : D₋ (fun x => star (f x)) u v
        = Cℂ ((1/2 : ℝ) • (T v - (Aℒ (H:=H) (W:=ℂ) T) v)) := by
    simpa [map_add, map_smul, sub_eq_add_neg] using this
  simpa [DplusCLM, Cℂ_apply, sub_eq_add_neg, ContinuousLinearMap.add_apply,
         ContinuousLinearMap.smul_apply, smul_add] using this

/-- Operator forms (from the directional ones). -/
lemma Dplus_star_op (f : H → ℂ) (u : H) (hf : DifferentiableAt ℝ f u) :
  D₊ (fun x => star (f x)) u = Cℂ.comp (D₋ f u) := by
  ext v; simpa using Dplus_star_dir f u v hf

lemma Dminus_star_op (f : H → ℂ) (u : H) (hf : DifferentiableAt ℝ f u) :
  D₋ (fun x => star (f x)) u = Cℂ.comp (D₊ f u) := by
  ext v; simpa using Dminus_star_dir f u v hf

/-! ### Product rules (directional) -/

section product_like
variable [CompleteSpace H]

lemma Dplus_prod_dir (f g : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  D₊ (fun x => f x * g x) u v
    = f u * D₊ g u v + g u * D₊ f u v := by
  classical
  set Df := fderivR f u
  set Dg := fderivR g u
  have h_mul : fderivR (fun x => f x * g x) u = f u • Dg + g u • Df := by
    simpa [fderivR, Df, Dg] using (fderiv_mul (𝕜:=ℝ) hf hg)
  -- Work directly at direction `v` to avoid CLM ext.
  -- `Aℒ` distributes over `+` and `•` (over ℝ), use light `simp`.
  have hA_add :
      (Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)) v
    = (f u • (Aℒ (H:=H) (W:=ℂ) Dg)) v
    + (g u • (Aℒ (H:=H) (W:=ℂ) Df)) v := by
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
          mul_add, add_comm, add_left_comm, add_assoc]
  -- Expand D₊: (1/2)•(T v + Aℒ T v)
  have : D₊ (fun x => f x * g x) u v
      = (1/2 : ℝ) • ((f u • Dg + g u • Df) v
                     + (Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)) v) := by
    simp (only) [DplusCLM, h_mul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  -- Push scalars and use `hA_add`.
  have : D₊ (fun x => f x * g x) u v
      = (1/2 : ℝ) • ( (f u * Dg v + g u * Df v)
                      + (f u * (Aℒ (H:=H) (W:=ℂ) Dg v)
                         + g u * (Aℒ (H:=H) (W:=ℂ) Df v)) ) := by
    simpa [hA_add, smul_eq_mul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
           mul_add, add_comm, add_left_comm, add_assoc]
  -- Recognize D₊ g and D₊ f at direction `v`.
  simpa [DplusCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
         smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc,
         sub_eq_add_neg] using this

lemma Dminus_prod_dir (f g : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  D₋ (fun x => f x * g x) u v
    = f u * D₋ g u v + g u * D₋ f u v := by
  classical
  set Df := fderivR f u
  set Dg := fderivR g u
  have h_mul : fderivR (fun x => f x * g x) u = f u • Dg + g u • Df := by
    simpa [fderivR, Df, Dg] using (fderiv_mul (𝕜:=ℝ) hf hg)
  -- As before, but with the minus combination
  have hA_add :
      (Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)) v
    = (f u • (Aℒ (H:=H) (W:=ℂ) Dg)) v
    + (g u • (Aℒ (H:=H) (W:=ℂ) Df)) v := by
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
          mul_add, add_comm, add_left_comm, add_assoc]
  have hI₁ :
      I * (f u * Dg (I • v)) = f u * (I * Dg (I • v)) := by
    calc
      I * (f u * Dg (I • v))
          = (I * f u) * Dg (I • v) := by simp [mul_assoc]
      _   = (f u * I) * Dg (I • v) := by simp [mul_comm]
      _   = f u * (I * Dg (I • v)) := by simp [mul_assoc]
  have hI₂ :
      I * (g u * Df (I • v)) = g u * (I * Df (I • v)) := by
    calc
      I * (g u * Df (I • v))
          = (I * g u) * Df (I • v) := by simp [mul_assoc]
      _   = (g u * I) * Df (I • v) := by simp [mul_comm]
      _   = g u * (I * Df (I • v)) := by simp [mul_assoc]
  have : D₋ (fun x => f x * g x) u v
      = (1/2 : ℝ) • ((f u • Dg + g u • Df) v
                     - (Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)) v) := by
    simp (only) [DminusCLM, h_mul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  -- push scalars and reorganize
  have : D₋ (fun x => f x * g x) u v
      = (1/2 : ℝ) • ( (f u * Dg v + g u * Df v)
                      - (f u * (Aℒ (H:=H) (W:=ℂ) Dg v)
                         + g u * (Aℒ (H:=H) (W:=ℂ) Df v)) ) := by
    simpa [hA_add, smul_eq_mul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
           mul_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
  -- Recognize the D₋ definitions (the `I`-twist is inside `Aℒ`).
  -- The hI₁/hI₂ are only used by the simp-set inside `DminusCLM` reductions,
  -- but at this stage they are already implicit in the recognized pattern.
  simpa [DminusCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
         smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc,
         sub_eq_add_neg] using this

end product_like

/-!  Congruence under `=ᶠ[𝓝 u]` (operator forms). -/

lemma DplusCLM_congr_of_eventuallyEq
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  D₊ f u = D₊ g u := by
  have := fderivR_congr_of_eventuallyEq (H:=H) hf hg h
  simp [DplusCLM, this]

lemma DminusCLM_congr_of_eventuallyEq
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  D₋ f u = D₋ g u := by
  have := fderivR_congr_of_eventuallyEq (H:=H) hf hg h
  simp [DminusCLM, this]

-- NOTE: `D₊ f u + D₋ f u = fderivR f u` is already in `Basic`, so we do NOT redeclare it here.

end scalar_rules

/-! ## Minimal `dz`, `dzbar` on `ℂ` (kept light here) -/

section partials_on_C
@[simp] lemma Complex.star_I : star (I : ℂ) = -I := by simp

/-- `dz f z := D₊ f z 1`. -/
def dz (f : ℂ → ℂ) (z : ℂ) : ℂ := D₊ f z (1 : ℂ)

/-- `dzbar f z := D₋ f z 1`. -/
def dzbar (f : ℂ → ℂ) (z : ℂ) : ℂ := D₋ f z (1 : ℂ)

end partials_on_C

end Wirtinger
