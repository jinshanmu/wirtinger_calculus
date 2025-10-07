import Mathlib
import WirtingerCalculus.Basic

/-!
First-order rules for scalar-valued maps over complex inner-product spaces.

Kept lean to avoid `simp` loops / heartbeats.
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
  -- Over ℝ, `star` commutes with real scalars.
  simp

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
  -- work pointwise to avoid unfolding everything:
  ext v
  have hI : star (I : ℂ) = -I := by simp
  simp [ContinuousLinearMap.comp_apply, Cℂ_apply, hI, sub_eq_add_neg]
end Aℒ_conj

/-! ## Congruence for `fderivR` under eventual equality -/

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

  -- Step 1: compute `(D₊ (star ∘ f) u) v` without expanding `star` or `Aℒ`.
  have h1a :
      (D₊ (fun x => star (f x)) u) v
        = (1/2 : ℝ) • ((Cℂ.comp T) v + (Aℒ (H:=H) (W:=ℂ) (Cℂ.comp T)) v) := by
    simp [DplusCLM, hDf,
          ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.comp_apply]

  -- Step 2: use `hA` pointwise and clean up to a `-` sign.
  have hApt :
      (Aℒ (H:=H) (W:=ℂ) (Cℂ.comp T)) v
        = - (Cℂ.comp (Aℒ (H:=H) (W:=ℂ) T)) v := by
    simpa using congrArg (fun K => K v) hA

  have h1 :
      (D₊ (fun x => star (f x)) u) v
        = (1/2 : ℝ) • (Cℂ (T v) - Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
    -- rewrite the second summand using `hApt`, then evaluate compositions
    -- and turn `+ (-x)` into `- x`.
    have := h1a
    -- rewrite the Aℒ term
    have := by
      simpa [hApt, ContinuousLinearMap.comp_apply] using this
    -- now simplify compositions and signs
    simpa [ContinuousLinearMap.comp_apply, Cℂ_apply, sub_eq_add_neg] using this

  -- Step 3: rewrite `star (D₋ f u v)` to the same RHS.
  have hDm :
      (D₋ f u) v = (1/2 : ℝ) • (T v - (Aℒ (H:=H) (W:=ℂ) T) v) := by
    simp [DminusCLM,
          ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply]

  have h2 :
      star ((D₋ f u) v)
        = (1/2 : ℝ) • (Cℂ (T v) - Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
    -- push `star` through a real smul and a subtraction
    rw [hDm, star_real_smul]
    change (1/2 : ℝ) • star (T v - (Aℒ (H:=H) (W:=ℂ) T) v) = _
    simpa [Cℂ_apply, sub_eq_add_neg, star_sub']  -- star distributes over `-`, becomes `Cℂ`

  exact h1.trans h2.symm

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

  have h1a :
      (D₋ (fun x => star (f x)) u) v
        = (1/2 : ℝ) • ((Cℂ.comp T) v - (Aℒ (H:=H) (W:=ℂ) (Cℂ.comp T)) v) := by
    simp [DminusCLM, hDf,
          ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.comp_apply, sub_eq_add_neg]

  have hApt :
      (Aℒ (H:=H) (W:=ℂ) (Cℂ.comp T)) v
        = - (Cℂ.comp (Aℒ (H:=H) (W:=ℂ) T)) v := by
    simpa using congrArg (fun K => K v) hA

  have h1 :
      (D₋ (fun x => star (f x)) u) v
        = (1/2 : ℝ) • (Cℂ (T v) + Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
    have := h1a
    have := by
      simpa [hApt, ContinuousLinearMap.comp_apply] using this
    simpa [ContinuousLinearMap.comp_apply, Cℂ_apply, sub_eq_add_neg] using this

  have hDp :
      (D₊ f u) v = (1/2 : ℝ) • (T v + (Aℒ (H:=H) (W:=ℂ) T) v) := by
    simp [DplusCLM,
          ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply]

  have h2 :
      star ((D₊ f u) v)
        = (1/2 : ℝ) • (Cℂ (T v) + Cℂ ((Aℒ (H:=H) (W:=ℂ) T) v)) := by
    rw [hDp, star_real_smul]
    change (1/2 : ℝ) • star (T v + (Aℒ (H:=H) (W:=ℂ) T) v) = _
    simpa [Cℂ_apply]  -- `star (a + b) = star a + star b`

  exact h1.trans h2.symm

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

  -- compute once, then distribute `Aℒ` pointwise without unfolding into `I`.
  have h0 :
      D₊ (fun x => f x * g x) u v
        = (1/2 : ℝ) •
          ((f u • Dg + g u • Df) v
           + (Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)) v) := by
    simp [DplusCLM, h_mul,
          ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply]

  -- Aℒ is ℝ-linear in its CLM argument; use the linearity lemmas provided by `Basic`.
  have hA_lin :
      Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)
        = f u • Aℒ (H:=H) (W:=ℂ) Dg + g u • Aℒ (H:=H) (W:=ℂ) Df := by
    -- If your `Basic` uses different names, replace `Aℒ_add`/`Aℒ_smul` below accordingly.
    simpa [Aℒ_add, Aℒ_smul]

  have hA :
      (Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)) v
        = (f u * (Aℒ (H:=H) (W:=ℂ) Dg v))
          + (g u * (Aℒ (H:=H) (W:=ℂ) Df v)) := by
    -- evaluate `hA_lin` at `v` and turn `•` into multiplication on ℂ
    have := congrArg (fun K => K v) hA_lin
    simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] using this

  -- also evaluate the scalar-smuls of CLMs at `v`
  have hv1 : (f u • Dg) v = f u * Dg v := by
    simpa [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hv2 : (g u • Df) v = g u * Df v := by
    simpa [ContinuousLinearMap.smul_apply, smul_eq_mul]

  -- combine and identify the two `D₊` pieces at direction `v`
  simpa [h0, hA, hv1, hv2, DplusCLM,
         ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
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

  have h0 :
      D₋ (fun x => f x * g x) u v
        = (1/2 : ℝ) •
          ((f u • Dg + g u • Df) v
           - (Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)) v) := by
    simp [DminusCLM, h_mul,
          ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply]

  have hA_lin :
      Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)
        = f u • Aℒ (H:=H) (W:=ℂ) Dg + g u • Aℒ (H:=H) (W:=ℂ) Df := by
    simpa [Aℒ_add, Aℒ_smul]

  have hA :
      (Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)) v
        = (f u * (Aℒ (H:=H) (W:=ℂ) Dg v))
          + (g u * (Aℒ (H:=H) (W:=ℂ) Df v)) := by
    have := congrArg (fun K => K v) hA_lin
    simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] using this

  have hv1 : (f u • Dg) v = f u * Dg v := by
    simpa [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hv2 : (g u • Df) v = g u * Df v := by
    simpa [ContinuousLinearMap.smul_apply, smul_eq_mul]

  -- keep everything in `•`/`*` form; don't expand `Aℒ`.
  simpa [h0, hA, hv1, hv2, DminusCLM,
         ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
         add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

end product_like

/-!  Congruence under `=ᶠ[𝓝 u]` (operator forms). -/

lemma DplusCLM_congr_of_eventuallyEq
  {H} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  D₊ f u = D₊ g u := by
  have := fderivR_congr_of_eventuallyEq (H:=H) hf hg h
  simp [DplusCLM, this]

lemma DminusCLM_congr_of_eventuallyEq
  {H} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  D₋ f u = D₋ g u := by
  have := fderivR_congr_of_eventuallyEq (H:=H) hf hg h
  simp [DminusCLM, this]

end scalar_rules

/-! ## Minimal `dz`, `dzbar` on `ℂ` -/

section partials_on_C
@[simp] lemma Complex.star_I : star (I : ℂ) = -I := by simp

/-- `dz f z := D₊ f z 1`. -/
def dz (f : ℂ → ℂ) (z : ℂ) : ℂ := D₊ f z (1 : ℂ)

/-- `dzbar f z := D₋ f z 1`. -/
def dzbar (f : ℂ → ℂ) (z : ℂ) : ℂ := D₋ f z (1 : ℂ)

end partials_on_C

end Wirtinger
