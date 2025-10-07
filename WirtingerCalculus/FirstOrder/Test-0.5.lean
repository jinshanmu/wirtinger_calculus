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
* Minimal definitions `dz`, `dzbar` on `ℂ` (no heavy 1D identity here).

All proofs avoid recursive `simp` patterns and only use small, targeted rewrites.
-/

noncomputable section
open Complex
open scoped ComplexInnerProductSpace Topology

namespace Wirtinger

-- Handy notations
local notation "D₊" => DplusCLM
local notation "D₋" => DminusCLM

/-! ## Real-linear conjugation on `ℂ` -/

@[simp] lemma star_add' (x y : ℂ) : star (x + y) = star x + star y := by simpa using Complex.conj_add _ _
@[simp] lemma star_mul' (x y : ℂ) : star (x * y) = star y * star x := by simpa using Complex.conj_mul _ _

/-- Real-linear complex conjugation on `ℂ` as a continuous linear map. -/
def Cℂ : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := star
  , map_add' := by intro x y; simpa using (star_add' x y)
  , map_smul' := by
      intro r z
      -- Over ℝ, `r • z = (r : ℂ) * z`
      -- `star (r:ℂ) = (r:ℂ)` and `star (a*b) = star b * star a`
      simpa [smul_eq_mul, star_mul', mul_comm, mul_left_comm, mul_assoc] },
  cont := continuous_star }

@[simp] lemma Cℂ_apply (z : ℂ) : Cℂ z = star z := rfl

/-- `J` anti-commutes with real-linear conjugation on `ℂ`. -/
lemma Jc_comp_Cℂ_anticom :
  (Jc ℂ).comp Cℂ = - (Cℂ.comp (Jc ℂ)) := by
  ext z
  have : star (I : ℂ) = -I := by simp
  -- LHS = I * star z; RHS = -(star (I * z)) = star z * I; equal in ℂ
  simp [Jc_apply, Cℂ_apply, star_mul', this, mul_comm, mul_left_comm, mul_assoc]

/-! ## Compatibility of `Aℒ` with conjugation -/

section Aℒ_conj
variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Compatibility of the anti-twist with conjugation. -/
lemma Aℒ_comp_Cℂ (T : H →L[ℝ] ℂ) :
  Aℒ (H:=H) (W:=ℂ) (Cℂ.comp T) = - Cℂ.comp (Aℒ (H:=H) (W:=ℂ) T) := by
  -- Prove pointwise: both sides are CLMs H →L[ℝ] ℂ
  ext v
  have : star (I : ℂ) = -I := by simp
  -- Expand the definition of `Aℒ` once and use `star_mul'`
  simp [Aℒ_apply, Cℂ_apply, ContinuousLinearMap.comp_apply,
        star_mul', this, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
end Aℒ_conj

/-! ## A basic congruence lemma for `fderivR` (needed later) -/

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
  -- Compute directly, keeping rewrites small
  have : D₊ (fun x => star (f x)) u v
        = (1/2 : ℝ) • ((Cℂ (T v)) + Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
    simp [DplusCLM, hDf, hA, ContinuousLinearMap.comp_apply, sub_eq_add_neg]
  -- Use ℝ-linearity of `Cℂ`
  have : D₊ (fun x => star (f x)) u v
        = Cℂ ((1/2 : ℝ) • (T v + (Aℒ (H:=H) (W:=ℂ) T) v)) := by
    simpa [smul_add, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul] using
      this
  -- Recognize `D₋ f u v`
  simpa [DminusCLM, Cℂ_apply] using this

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
    simp [DminusCLM, hDf, hA, ContinuousLinearMap.comp_apply, add_comm, add_left_comm, add_assoc]
  have : D₋ (fun x => star (f x)) u v
        = Cℂ ((1/2 : ℝ) • (T v - (Aℒ (H:=H) (W:=ℂ) T) v)) := by
    simpa [smul_sub, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
           sub_eq_add_neg] using this
  simpa [DplusCLM, Cℂ_apply, sub_eq_add_neg] using this

/-- Operator forms (from the directional ones) -/
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
  have h_mul : fderivR (fun x => f x * g x) u = f u • Dg + g u • Df :=
    fderiv_mul hf hg
  -- `Aℒ` distributes over `+` and `•` (as ℝ-linear)
  have hA_add : Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)
                = f u • Aℒ (H:=H) (W:=ℂ) Dg + g u • Aℒ (H:=H) (W:=ℂ) Df := by
    ext w; simp [Aℒ_apply, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc]
  -- Prove operator equality by `ext v`
  have : D₊ (fun x => f x * g x) u
        = f u • D₊ g u + g u • D₊ f u := by
    ext w
    -- Evaluate `D₊` pointwise using the definitions
    simp [DplusCLM, h_mul, hA_add, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul, sub_eq_add_neg,
          add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc]
  -- Turn it into a directional identity
  simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] using congrArg (fun L => L v) this

lemma Dminus_prod_dir (f g : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  D₋ (fun x => f x * g x) u v
    = f u * D₋ g u v + g u * D₋ f u v := by
  classical
  set Df := fderivR f u
  set Dg := fderivR g u
  have h_mul : fderivR (fun x => f x * g x) u = f u • Dg + g u • Df :=
    fderiv_mul hf hg
  have hA_add : Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)
                = f u • Aℒ (H:=H) (W:=ℂ) Dg + g u • Aℒ (H:=H) (W:=ℂ) Df := by
    ext w; simp [Aℒ_apply, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc]
  have : D₋ (fun x => f x * g x) u
        = f u • D₋ g u + g u • D₋ f u := by
    ext w
    simp [DminusCLM, h_mul, hA_add, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul,
          add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc]
  simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] using congrArg (fun L => L v) this

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

end scalar_rules

/-! ## Minimal `dz`, `dzbar` on `ℂ` (kept light here) -/

section partials_on_C
@[simp] lemma Complex.star_I : star (I : ℂ) = -I := by simpa

/-- `dz f z := D₊ f z 1`. -/
def dz (f : ℂ → ℂ) (z : ℂ) : ℂ := D₊ f z (1 : ℂ)

/-- `dzbar f z := D₋ f z 1`. -/
def dzbar (f : ℂ → ℂ) (z : ℂ) : ℂ := D₋ f z (1 : ℂ)

end partials_on_C

end Wirtinger
