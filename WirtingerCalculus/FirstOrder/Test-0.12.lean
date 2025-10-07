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

@[simp] lemma star_sub' (x y : ℂ) : star (x - y) = star x - star y := by
  simp [sub_eq_add_neg]

@[simp] lemma star_mul' (x y : ℂ) : star (x * y) = star x * star y := by
  simp

@[simp] lemma ofReal_mul_I (r : ℝ) : (r : ℂ) * I = I * (r : ℂ) := by
  simp [mul_comm]

@[simp] lemma smul_one_real (r : ℝ) : r • (1 : ℂ) = (r : ℂ) := by
  simp

@[simp] lemma smul_I_real (r : ℝ) : r • (I : ℂ) = (r : ℂ) * I := by
  simp

@[simp] lemma star_real_smul (r : ℝ) (z : ℂ) : star (r • z) = r • star z := by
  -- use `r • z = (r : ℂ) * z` and multiplicativity of `star`
  simp [smul_eq_mul]

/-! ## Real-linear conjugation on `ℂ` -/

/-- Real-linear complex conjugation on `ℂ` as a continuous linear map. -/
def Cℂ : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := star
  , map_add' := by intro x y; simp
  , map_smul' := by intro r z; simp },
  cont := continuous_star }

@[simp] lemma Cℂ_apply (z : ℂ) : Cℂ z = star z := rfl

/-- `J` anti-commutes with real-linear conjugation on `ℂ`. -/
lemma Jc_comp_Cℂ_anticom :
  (Jc ℂ).comp Cℂ = - (Cℂ.comp (Jc ℂ)) := by
  ext z
  have hI : star (I : ℂ) = -I := by simp
  -- LHS = I * star z; RHS = -(star (I * z)) = - (star I * star z) = I * star z.
  simp [ContinuousLinearMap.comp_apply, Jc_apply, Cℂ_apply, hI]

/-! ## Compatibility of `Aℒ` with conjugation -/

section Aℒ_conj
variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Compatibility of the anti-twist with conjugation. -/
lemma Aℒ_comp_Cℂ (T : H →L[ℝ] ℂ) :
  Aℒ (H:=H) (W:=ℂ) (Cℂ.comp T)
    = - Cℂ.comp (Aℒ (H:=H) (W:=ℂ) T) := by
  -- expand via the definition used in `Basic` (sandwich with `Jc`)
  ext v
  have hI : star (I : ℂ) = -I := by simp
  simp [ContinuousLinearMap.comp_apply, Cℂ_apply, hI, sub_eq_add_neg]
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
  have hfg : HasFDerivAt g (fderivR f u) u := hf'.congr_of_eventuallyEq h.symm
  have huniq : fderivR g u = fderivR f u := hg'.unique hfg
  simpa using huniq.symm

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
  have hA :
      Aℒ (H:=H) (W:=ℂ) ((Cℂ : ℂ →L[ℝ] ℂ).comp T)
        = - (Cℂ : ℂ →L[ℝ] ℂ).comp (Aℒ (H:=H) (W:=ℂ) T) :=
    Aℒ_comp_Cℂ (H:=H) (T := T)
  -- expand `D₊`
  have h1 :
      (D₊ (fun x => star (f x)) u) v
        = (1/2 : ℝ) •
          (Cℂ (T v) - Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
    -- from definitions: the minus comes from `hA`
    simp [DplusCLM, hDf, hA, ContinuousLinearMap.comp_apply,
          sub_eq_add_neg, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply]
  -- rewrite RHS as `star (D₋ f u v)`
  have h2 :
      star ((D₋ f u) v)
        = (1/2 : ℝ) •
          (Cℂ (T v) - Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
    -- expand `D₋`, then push `star` in using real-smul lemma
    calc
      star ((D₋ f u) v)
          = star ((1/2 : ℝ) •
                (T v - (Aℒ (H:=H) (W:=ℂ) T) v)) := by
                  simp [DminusCLM, sub_eq_add_neg]
      _ = (1/2 : ℝ) •
            star (T v - (Aℒ (H:=H) (W:=ℂ) T) v) := by
              simp [star_real_smul]
      _ = (1/2 : ℝ) •
            (Cℂ (T v) - Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
              simp [Cℂ_apply, sub_eq_add_neg]
  simpa [h1, h2]

lemma Dminus_star_dir (f : H → ℂ) (u v : H) (hf : DifferentiableAt ℝ f u) :
  D₋ (fun x => star (f x)) u v = star (D₊ f u v) := by
  classical
  set T := fderivR f u
  have hDf :
      fderivR (fun x => star (f x)) u = (Cℂ : ℂ →L[ℝ] ℂ).comp T :=
    ((Cℂ : ℂ →L[ℝ] ℂ).hasFDerivAt.comp u hf.hasFDerivAt).fderiv
  have hA :
      Aℒ (H:=H) (W:=ℂ) ((Cℂ : ℂ →L[ℝ] ℂ).comp T)
        = - (Cℂ : ℂ →L[ℝ] ℂ).comp (Aℒ (H:=H) (W:=ℂ) T) :=
    Aℒ_comp_Cℂ (H:=H) (T := T)
  have h1 :
      (D₋ (fun x => star (f x)) u) v
        = (1/2 : ℝ) •
          (Cℂ (T v) + Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
    -- for `D₋`, the sign flips to a `+` after using `hA`
    simp [DminusCLM, hDf, hA, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have h2 :
      star ((D₊ f u) v)
        = (1/2 : ℝ) •
          (Cℂ (T v) + Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
    calc
      star ((D₊ f u) v)
          = star ((1/2 : ℝ) • (T v + (Aℒ (H:=H) (W:=ℂ) T) v)) := by
              simp [DplusCLM]
      _ = (1/2 : ℝ) • star (T v + (Aℒ (H:=H) (W:=ℂ) T) v) := by
              simp [star_real_smul]
      _ = (1/2 : ℝ) •
            (Cℂ (T v) + Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
              simp [Cℂ_apply]
  simpa [h1, h2]

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
  -- expand at direction `v`
  have :
      D₊ (fun x => f x * g x) u v
        = (1/2 : ℝ) •
          ((f u • Dg + g u • Df) v
           + (Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)) v) := by
    simp [DplusCLM, h_mul, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply]
  -- push scalars and distribute `Aℒ`
  have hA :
      (Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)) v
        = (f u * (Aℒ (H:=H) (W:=ℂ) Dg v))
          + (g u * (Aℒ (H:=H) (W:=ℂ) Df v)) := by
    -- definition of `Aℒ` is linear in `T` and commutes with scalar multiplication
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_add]
  -- finish by recognizing `D₊ g u v` and `D₊ f u v`
  simpa [this, hA, DplusCLM, ContinuousLinearMap.add_apply,
         ContinuousLinearMap.smul_apply, smul_eq_mul, mul_add,
         add_comm, add_left_comm, add_assoc]

lemma Dminus_prod_dir (f g : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  D₋ (fun x => f x * g x) u v
    = f u * D₋ g u v + g u * D₋ f u v := by
  classical
  set Df := fderivR f u
  set Dg := fderivR g u
  have h_mul : fderivR (fun x => f x * g x) u = f u • Dg + g u • Df := by
    simpa [fderivR, Df, Dg] using (fderiv_mul (𝕜:=ℝ) hf hg)
  have :
      D₋ (fun x => f x * g x) u v
        = (1/2 : ℝ) •
          ((f u • Dg + g u • Df) v
           - (Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)) v) := by
    simp [DminusCLM, h_mul, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply]
  have hA :
      (Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)) v
        = (f u * (Aℒ (H:=H) (W:=ℂ) Dg v))
          + (g u * (Aℒ (H:=H) (W:=ℂ) Df v)) := by
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul, add_comm, add_left_comm, add_assoc, mul_add]
  -- a couple of tiny algebraic reshuffles with `I` never appear here,
  -- because we keep `Aℒ` abstract and only unfold at the end
  simpa [this, hA, DminusCLM, ContinuousLinearMap.add_apply,
         ContinuousLinearMap.smul_apply, smul_eq_mul, mul_add,
         add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

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

-- NOTE: `D₊ f u + D₋ f u = fderivR f u` is already in `Basic`.

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
