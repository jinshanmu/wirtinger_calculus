import Mathlib
import WirtingerCalculus.Basic

/-!
First-order rules and utilities for the Wirtinger development.

No `admit`/`sorry`.
-/

noncomputable section
open Complex Topology
open scoped ComplexInnerProductSpace

namespace Wirtinger

/-! ## Star lemmas on `ℂ` (binder names explicit) -/

@[simp] lemma star_add' (x y : ℂ) : star (x + y) = star x + star y := by
  simpa using (star_add (r:=x) (s:=y))

@[simp] lemma star_mul' (x y : ℂ) : star (x * y) = star y * star x := by
  simpa using (star_mul (r:=x) (s:=y))

@[simp] lemma star_ofReal' (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
  simpa using (star_ofReal r)

@[simp] lemma Complex.star_I : star (I : ℂ) = -I := by
  simpa using Complex.conj_I

/-! ## Real-linear complex conjugation as a CLM -/

def Cℂ : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := fun z => star z
  , map_add' := by
      intro x y; simpa using (star_add' x y)
  , map_smul' := by
      intro r z
      have h1 : star ((r : ℂ) * z) = star z * (r : ℂ) := by
        simpa [star_ofReal'] using (star_mul' (x:=(r:ℂ)) (y:=z))
      -- commute the (real) scalar with the complex number
      simpa [mul_comm] using h1 }
, cont := continuous_star }

@[simp] lemma Cℂ_apply (z : ℂ) : Cℂ z = star z := rfl

/-- `J` anti-commutes with `Cℂ` on `ℂ`. -/
lemma Jc_comp_Cℂ_anticom :
  (Jc ℂ).comp Cℂ = - (Cℂ.comp (Jc ℂ)) := by
  ext z
  simp [Jc_apply, Cℂ_apply, star_mul', Complex.star_I,
        mul_comm, mul_left_comm, mul_assoc]

/-! ## Key compatibility of the anti-twist with conjugation -/

section AL_twist
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Compatibility of `Aℒ` with real-linear conjugation `Cℂ`. -/
lemma Aℒ_comp_Cℂ (T : H →L[ℝ] ℂ) :
  Aℒ (H:=H) (W:=ℂ) (Cℂ.comp T) = - Cℂ.comp (Aℒ (H:=H) (W:=ℂ) T) := by
  ext v
  -- goal reduces to `I * star (T (I • v)) = - star (I * T (I • v))`
  simp [Aℒ_apply, Cℂ_apply, ContinuousLinearMap.comp_apply,
        star_mul', Complex.star_I, mul_comm, mul_left_comm, mul_assoc]
end AL_twist

/-! ## Conjugation rules for scalar targets -/

section scalar_rules
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Operator form: `D₊(conj ∘ f) = Cℂ ∘L D₋ f`. -/
lemma Dplus_star_op (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) :
    DplusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u
      = Cℂ.comp (DminusCLM (H:=H) (W:=ℂ) f u) := by
  classical
  set D := fderivR (H:=H) (W:=ℂ) f u
  have hDf :
      fderivR (H:=H) (W:=ℂ) (fun x => star (f x)) u = Cℂ.comp D := by
    -- Ensure definally the same function as `Cℂ ∘ f`
    simpa [Function.comp, Cℂ_apply, star_eq_re_sub_im] using
      ((Cℂ.hasFDerivAt).comp u hf.hasFDerivAt).fderiv
  have hA := Aℒ_comp_Cℂ (H:=H) (T:=D)
  simp [DplusCLM, DminusCLM, hDf, hA, sub_eq_add_neg,
        ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]

/-- Operator form: `D₋(conj ∘ f) = Cℂ ∘L D₊ f`. -/
lemma Dminus_star_op (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) :
    DminusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u
      = Cℂ.comp (DplusCLM (H:=H) (W:=ℂ) f u) := by
  classical
  set D := fderivR (H:=H) (W:=ℂ) f u
  have hDf :
      fderivR (H:=H) (W:=ℂ) (fun x => star (f x)) u = Cℂ.comp D := by
    simpa [Function.comp, Cℂ_apply, star_eq_re_sub_im] using
      ((Cℂ.hasFDerivAt).comp u hf.hasFDerivAt).fderiv
  have hA := Aℒ_comp_Cℂ (H:=H) (T:=D)
  simp [DminusCLM, DplusCLM, hDf, hA,
        ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_smul]

/-- Pointwise (directional) forms. -/
@[simp] lemma Dplus_star_dir (f : H → ℂ) (u v : H) (hf : DifferentiableAt ℝ f u) :
  DplusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u v
    = star (DminusCLM (H:=H) (W:=ℂ) f u v) := by
  simpa using congrArg (fun L => L v) (Dplus_star_op (H:=H) f u hf)

@[simp] lemma Dminus_star_dir (f : H → ℂ) (u v : H) (hf : DifferentiableAt ℝ f u) :
  DminusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u v
    = star (DplusCLM (H:=H) (W:=ℂ) f u v) := by
  simpa using congrArg (fun L => L v) (Dminus_star_op (H:=H) f u hf)

/-! ### Product rules -/

section product_like
variable [CompleteSpace H]

/-- helper: commute `I` through products in `ℂ` -/
@[simp] lemma I_left_pull (a b : ℂ) : I * (a * b) = a * (I * b) := by
  ring

/-- **Directional product rule** for `D₊`. -/
lemma Dplus_prod_dir (f g : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  DplusCLM (H:=H) (W:=ℂ) (fun x => f x * g x) u v
    = f u * DplusCLM (H:=H) (W:=ℂ) g u v
      + g u * DplusCLM (H:=H) (W:=ℂ) f u v := by
  classical
  set Df := fderivR (H:=H) (W:=ℂ) f u
  set Dg := fderivR (H:=H) (W:=ℂ) g u
  have h_mul : fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u
      = f u • Dg + g u • Df := by
    simpa using fderiv_mul (x:=u) hf hg
  have hAop :
    Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)
      = f u • Aℒ (H:=H) (W:=ℂ) Dg + g u • Aℒ (H:=H) (W:=ℂ) Df := by
    ext w; simp [Aℒ_apply, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc]
  have hop :
    DplusCLM (H:=H) (W:=ℂ) (fun x => f x * g x) u
      = f u • DplusCLM (H:=H) (W:=ℂ) g u
        + g u • DplusCLM (H:=H) (W:=ℂ) f u := by
    ext w
    simp [DplusCLM, h_mul, hAop, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul,
          sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc]
  simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] using
    congrArg (fun L => L v) hop

/-- **Directional product rule** for `D₋`. -/
lemma Dminus_prod_dir (f g : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  DminusCLM (H:=H) (W:=ℂ) (fun x => f x * g x) u v
    = f u * DminusCLM (H:=H) (W:=ℂ) g u v
      + g u * DminusCLM (H:=H) (W:=ℂ) f u v := by
  classical
  set Df := fderivR (H:=H) (W:=ℂ) f u
  set Dg := fderivR (H:=H) (W:=ℂ) g u
  have h_mul : fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u
      = f u • Dg + g u • Df := by
    simpa using fderiv_mul (x:=u) hf hg
  have hAop :
    Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)
      = f u • Aℒ (H:=H) (W:=ℂ) Dg + g u • Aℒ (H:=H) (W:=ℂ) Df := by
    ext w; simp [Aℒ_apply, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc]
  have hop :
    DminusCLM (H:=H) (W:=ℂ) (fun x => f x * g x) u
      = f u • DminusCLM (H:=H) (W:=ℂ) g u
        + g u • DminusCLM (H:=H) (W:=ℂ) f u := by
    ext w
    simp [DminusCLM, h_mul, hAop, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul,
          add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc]
  simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] using
    congrArg (fun L => L v) hop

end product_like

/-!  Congruence under `=ᶠ[𝓝 u]` -/
section congr_helpers

/-- If `f =ᶠ[𝓝 u] g`, their real Fréchet derivatives at `u` are equal. -/
lemma fderivR_congr_of_eventuallyEq
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  fderivR (H:=H) (W:=ℂ) f u = fderivR (H:=H) (W:=ℂ) g u := by
  classical
  have hf' := hf.hasFDerivAt
  have hg' := hg.hasFDerivAt
  have hfg : HasFDerivAt g (fderivR (H:=H) (W:=ℂ) f u) u :=
    hf'.congr_of_eventuallyEq h.symm
  have : fderivR (H:=H) (W:=ℂ) g u
        = fderivR (H:=H) (W:=ℂ) f u := hg'.unique hfg
  simpa using this.symm

lemma DplusCLM_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  DplusCLM (H:=H) (W:=ℂ) f u = DplusCLM (H:=H) (W:=ℂ) g u := by
  simp [DplusCLM, fderivR_congr_of_eventuallyEq (H:=H) hf hg h]

lemma DminusCLM_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  DminusCLM (H:=H) (W:=ℂ) f u = DminusCLM (H:=H) (W:=ℂ) g u := by
  simp [DminusCLM, fderivR_congr_of_eventuallyEq (H:=H) hf hg h]

end congr_helpers

/-! ## Formal partials on `ℂ` -/

section partials_on_C
variable [CompleteSpace ℂ]

/-- `dz f z := D₊ f z 1`. -/
def dz (f : ℂ → ℂ) (z : ℂ) : ℂ := DplusCLM (H:=ℂ) (W:=ℂ) f z (1 : ℂ)

/-- `dzbar f z := D₋ f z 1`. -/
def dzbar (f : ℂ → ℂ) (z : ℂ) : ℂ := DminusCLM (H:=ℂ) (W:=ℂ) f z (1 : ℂ)

/-- On `ℂ`, the real Fréchet derivative decomposes as
`D f(u) w = dz f u * w + dzbar f u * star w`. -/
lemma fderiv_via_partials (f : ℂ → ℂ) (u w : ℂ) :
  fderivR (H:=ℂ) (W:=ℂ) f u w
    = dz f u * w + dzbar f u * star w := by
  classical
  -- abbreviate
  set D := fderivR (H:=ℂ) (W:=ℂ) f u
  -- values on `1` and `I`
  have h1 : D 1 = dz f u + dzbar f u := by
    simpa [dz, dzbar] using
      (fderivR_apply_split (H:=ℂ) (W:=ℂ) (f:=f) (u:=u) (v:=1))
  have hI : D I = I * dz f u - I * dzbar f u := by
    have hplus :
        DplusCLM (H:=ℂ) (W:=ℂ) f u I = I * dz f u := by
      simpa [dz, Jc_apply, smul_eq_mul] using
        (Dplus_comm_J_point (H:=ℂ) (W:=ℂ) (f:=f) (u:=u) (v:=1))
    have hminus :
        DminusCLM (H:=ℂ) (W:=ℂ) f u I = - I * dzbar f u := by
      simpa [dzbar, Jc_apply, smul_eq_mul] using
        (Dminus_anticomm_J_point (H:=ℂ) (W:=ℂ) (f:=f) (u:=u) (v:=1))
    have : D I
        = DplusCLM (H:=ℂ) (W:=ℂ) f u I + DminusCLM (H:=ℂ) (W:=ℂ) f u I :=
      fderivR_apply_split (H:=ℂ) (W:=ℂ) (f:=f) (u:=u) (v:=I)
    simpa [hplus, hminus, sub_eq_add_neg] using this
  -- decompose `w` and use ℝ-linearity of `D`
  have hwC : (w.re : ℂ) + (w.im : ℂ) * I = w := Complex.re_add_im w
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • I := by
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hwC.symm
  have hsmul1 : D ((w.re : ℝ) • (1 : ℂ)) = (w.re : ℝ) • D 1 := by
    simpa using (D.map_smul (w.re : ℝ) (1 : ℂ))
  have hsmul2 : D ((w.im : ℝ) • I) = (w.im : ℝ) • D I := by
    simpa using (D.map_smul (w.im : ℝ) (I))
  have hlin :
      D ((w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • I)
        = (w.re : ℝ) • D 1 + (w.im : ℝ) • D I := by
    simpa [hsmul1, hsmul2] using
      (D.map_add ((w.re : ℝ) • (1 : ℂ)) ((w.im : ℝ) • I))
  calc
    D w
        = D ((w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • I) := by
            simpa [hw]
    _   = (w.re : ℝ) • D 1 + (w.im : ℝ) • D I := hlin
    _   = (w.re : ℂ) * (dz f u + dzbar f u)
          + (w.im : ℂ) * (I * dz f u - I * dzbar f u) := by
            simpa [smul_eq_mul, h1, hI]
    _   = dz f u * w + dzbar f u * star w := by
      have hw' : w = (w.re : ℂ) + (w.im : ℂ) * I := by simpa using hwC
      have hstarw : star w = (w.re : ℂ) - (w.im : ℂ) * I := by
        simpa [star_eq_re_sub_im w]
      ring_nf
      simpa [hw', hstarw, mul_add, add_mul, sub_eq_add_neg,
             mul_comm, mul_left_comm, mul_assoc]
end partials_on_C

end scalar_rules
end Wirtinger
