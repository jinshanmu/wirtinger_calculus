import Mathlib
import WirtingerCalculus.Basic

/-!
First-order rules needed in your tests. Main points:

* Define real-linear conjugation `Cℂ : ℂ →L[ℝ] ℂ` via `star`.
* Prove the compatibility lemma `Aℒ_comp_Cℂ`.
* Conjugation rules for `D₊`/`D₋` (operator and directional forms).
* Product rules for `D₊`/`D₋` and corresponding gradient product rules.
* Congruence lemmas under `=ᶠ[𝓝 u]` (including the `fderivR_congr_of_eventuallyEq`
  you call later).
* One-dimensional “partials” identity on `ℂ`.

All proofs are self-contained; no `admit`/`sorry`.
-/

noncomputable section
open Complex Topology
open scoped ComplexInnerProductSpace

namespace Wirtinger

/-! ## Helpers on `ℂ` and real-linear conjugation -/

@[simp] lemma star_add' (x y : ℂ) : star (x + y) = star x + star y := by
  simpa using (star_add (x:=x) (y:=y))

@[simp] lemma star_mul' (x y : ℂ) : star (x * y) = star y * star x := by
  simpa using (star_mul (x:=x) (y:=y))

@[simp] lemma star_ofReal' (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
  simpa using (star_ofReal r)

@[simp] lemma Complex.star_I : star (I : ℂ) = -I := by
  simpa using Complex.conj_I

/-- Real-linear complex conjugation on `ℂ`. -/
def Cℂ : ℂ →L[ℝ] ℂ :=
{ toLinearMap :=
  { toFun := fun z => star z
  , map_add' := by intro x y; simpa using (star_add' x y)
  , map_smul' := by
      intro r z
      -- interpret ℝ-scaling as `(r:ℂ) * z`
      change star ((r : ℂ) * z) = (r : ℂ) * star z
      -- `star (a*b) = star b * star a` and reals commute
      have := by
        simpa [star_mul', star_ofReal'] :
          star ((r : ℂ) * z) = star z * (r : ℂ)
      simpa [mul_comm] using this }
, cont := continuous_star }

@[simp] lemma Cℂ_apply (z : ℂ) : Cℂ z = star z := rfl

/-- `J` anti-commutes with `Cℂ` on `ℂ`. -/
lemma Jc_comp_Cℂ_anticom :
  (Jc ℂ).comp Cℂ = - (Cℂ.comp (Jc ℂ)) := by
  ext z
  -- LHS: I * star z; RHS: - star (I*z)
  simp [Jc_apply, Cℂ_apply, star_mul', Complex.star_I, mul_comm, mul_left_comm, mul_assoc]

/-! ### Key: compatibility of the anti-twist with conjugation -/
section AL_twist
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Compatibility of `Aℒ` with real-linear conjugation `Cℂ`. -/
lemma Aℒ_comp_Cℂ (T : H →L[ℝ] ℂ) :
  Aℒ (H:=H) (W:=ℂ) (Cℂ.comp T) = - Cℂ.comp (Aℒ (H:=H) (W:=ℂ) T) := by
  ext v
  -- goal becomes: `I * star (T (I • v)) = - star (I * T (I • v))`
  simp [Aℒ_apply, Cℂ_apply, ContinuousLinearMap.comp_apply,
        star_mul', Complex.star_I, mul_comm, mul_left_comm, mul_assoc]
end AL_twist

/-! ## Scalar-valued rules on a complex Hilbert space -/

section scalar_rules
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Conjugation via `star` -/

/-- Operator form: `D₊(star ∘ f) = Cℂ ∘L D₋ f`. -/
lemma Dplus_star_op (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) :
    DplusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u
      = Cℂ.comp (DminusCLM (H:=H) (W:=ℂ) f u) := by
  classical
  let D := fderivR (H:=H) (W:=ℂ) f u
  have hDf : fderivR (H:=H) (W:=ℂ) (fun x => star (f x)) u = Cℂ.comp D := by
    simpa using ((Cℂ.hasFDerivAt).comp u hf.hasFDerivAt).fderiv
  have hA := Aℒ_comp_Cℂ (H:=H) (T:=D)
  -- unfold and tidy:
  simp [DplusCLM, DminusCLM, hDf, hA, sub_eq_add_neg,
        ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]

/-- Operator form: `D₋(star ∘ f) = Cℂ ∘L D₊ f`. -/
lemma Dminus_star_op (f : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) :
    DminusCLM (H:=H) (W:=ℂ) (fun x => star (f x)) u
      = Cℂ.comp (DplusCLM (H:=H) (W:=ℂ) f u) := by
  classical
  let D := fderivR (H:=H) (W:=ℂ) f u
  have hDf : fderivR (H:=H) (W:=ℂ) (fun x => star (f x)) u = Cℂ.comp D := by
    simpa using ((Cℂ.hasFDerivAt).comp u hf.hasFDerivAt).fderiv
  have hA := Aℒ_comp_Cℂ (H:=H) (T:=D)
  simp [DminusCLM, DplusCLM, hDf, hA,
        ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_smul]

/-- Directional forms. -/
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

/-- **Directional product rule** for `D₊`. -/
lemma Dplus_prod_dir (f g : H → ℂ) (u v : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  DplusCLM (H:=H) (W:=ℂ) (fun x => f x * g x) u v
    = f u * DplusCLM (H:=H) (W:=ℂ) g u v
      + g u * DplusCLM (H:=H) (W:=ℂ) f u v := by
  classical
  let Df := fderivR (H:=H) (W:=ℂ) f u
  let Dg := fderivR (H:=H) (W:=ℂ) g u
  have h_mul : fderivR (H:=H) (W:=ℂ) (fun x => f x * g x) u
      = f u • Dg + g u • Df := by
    simpa using fderiv_mul (x:=u) hf hg
  -- `Aℒ` distributes
  have hAop :
    Aℒ (H:=H) (W:=ℂ) (f u • Dg + g u • Df)
      = f u • Aℒ (H:=H) (W:=ℂ) Dg + g u • Aℒ (H:=H) (W:=ℂ) Df := by
    ext w; simp [Aℒ_apply, smul_eq_mul, mul_add, add_comm, add_left_comm, add_assoc]
  -- operator identity, then evaluate at `v`
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
  let Df := fderivR (H:=H) (W:=ℂ) f u
  let Dg := fderivR (H:=H) (W:=ℂ) g u
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

/-- **Gradient product rules.** -/
lemma grad_prod (f g : H → ℂ) (u : H)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u) :
  ∇₊ (H:=H) f u = star (g u) • ∇₊ f u + star (f u) • ∇₊ g u
∧ ∇₋ (H:=H) f u = g u • ∇₋ f u + f u • ∇₋ g u := by
  constructor
  · -- `∇₊` case: compare dual functionals
    classical
    -- Show the functionals are equal, then apply `(toDual).symm` injectivity via definition
    have hfun :
      (InnerProductSpace.toDual ℂ H) (∇₊ (H:=H) (fun x => f x * g x) u)
        = (InnerProductSpace.toDual ℂ H)
            (star (g u) • ∇₊ f u + star (f u) • ∇₊ g u) := by
      ext v
      -- LHS = `D₊(fg) v`, RHS expands with inner properties
      have := Dplus_prod_dir (H:=H) f g u v hf hg
      -- turn RHS into inner expressions
      -- `inner (a•x) v = star a * inner x v`
      -- and `inner (x+y) v = inner x v + inner y v`
      -- also `inner (∇₊ h u) v = D₊ h u v`
      simp [inner_gradPlus_eq_Dplus, this, inner_add_left, inner_smul_left,
            mul_comm, add_comm, add_left_comm, add_assoc]
    -- now rewrite definition of `gradPlus`
    -- `(toDual) (gradPlus (fg)) = DplusCLM_c_linear (fg)`
    -- and `(toDual) (star(g u)•…)` is the functional `v ↦ inner (…) v`
    -- so equality above implies the desired vector equality
    -- because `gradPlus` is defined via `(toDual).symm`
    -- Apply `(toDual).symm` to both sides and simplify.
    have := congrArg (fun Φ => (InnerProductSpace.toDual ℂ H).symm Φ) hfun
    simpa [gradPlus] using this
  · -- `∇₋` case: start from directional rule, compare inner on the *right*, then flip
    classical
    -- First show: for all `v`, `⟪v, ∇₋(fg) u⟫ = ⟪v, g u • ∇₋ f u + f u • ∇₋ g u⟫`
    have h_right : ∀ v, inner (𝕜 := ℂ) v (∇₋ (H:=H) (fun x => f x * g x) u)
                  = inner (𝕜 := ℂ) v (g u • ∇₋ f u + f u • ∇₋ g u) := by
      intro v
      -- Use the `D₋` directional product rule and the Riesz bridge for `∇₋`.
      have := Dminus_prod_dir (H:=H) f g u v hf hg
      -- `D₋ h u v = ⟪v, ∇₋ h u⟫`
      -- and `⟪v, a•w⟫ = a * ⟪v, w⟫`, `⟪v, x+y⟫ = ⟪v,x⟫ + ⟪v,y⟫`
      simpa [Dminus_eq_inner_gradMinus, inner_add_right, inner_smul_right,
             mul_comm, add_comm, add_left_comm, add_assoc] using this
    -- Turn equality of right-inners into equality of left-inners via conjugation,
    -- then proceed as in the `∇₊` case with `(toDual).symm`.
    have h_left :
      (InnerProductSpace.toDual ℂ H) (∇₋ (H:=H) (fun x => f x * g x) u)
        = (InnerProductSpace.toDual ℂ H)
            (g u • ∇₋ f u + f u • ∇₋ g u) := by
      ext v
      -- Use `inner_conj_symm`: `⟪x,y⟫ = star ⟪y,x⟫`
      have := congrArg star (h_right v)
      simpa [inner_conj_symm, star_add, star_mul] using this
    have := congrArg (fun Φ => (InnerProductSpace.toDual ℂ H).symm Φ) h_left
    simpa [gradMinus] using this

end product_like

/-!  Congruence under `=ᶠ[𝓝 u]`. -/
section congr_helpers

/-- If `f =ᶠ[𝓝 u] g`, their real Fréchet derivatives at `u` are equal.
This is the name your test file expects. -/
lemma fderivR_congr_of_eventuallyEq
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  fderivR (H:=H) (W:=ℂ) f u = fderivR (H:=H) (W:=ℂ) g u := by
  classical
  -- Use `HasFDerivAt.congr_of_eventuallyEq` and uniqueness of the derivative.
  have hf' := hf.hasFDerivAt
  have hg' := hg.hasFDerivAt
  have hfg : HasFDerivAt g (fderivR (H:=H) (W:=ℂ) f u) u :=
    hf'.congr_of_eventuallyEq h.symm
  -- uniqueness of the derivative for `g`
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

lemma gradPlus_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  ∇₊ (H:=H) f u = ∇₊ g u := by
  classical
  -- Compare the dual functionals, then apply `(toDual).symm`.
  have hfun :
    (InnerProductSpace.toDual ℂ H) (∇₊ (H:=H) f u)
      = (InnerProductSpace.toDual ℂ H) (∇₊ g u) := by
    -- Both sides are `DplusCLM_c_linear …`
    simp [gradPlus, DplusCLM_congr_of_eventuallyEq (H:=H) hf hg h]
  simpa [gradPlus] using
    congrArg (fun Φ => (InnerProductSpace.toDual ℂ H).symm Φ) hfun

lemma gradMinus_congr_of_eventuallyEq {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {f g : H → ℂ} {u : H}
  (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
  (h : f =ᶠ[𝓝 u] g) :
  ∇₋ (H:=H) f u = ∇₋ g u := by
  classical
  -- Use right-inner characterization, then flip by conjugation as in `grad_prod` (minus case).
  have h_right : ∀ v, inner (𝕜 := ℂ) v (∇₋ (H:=H) f u)
                    = inner (𝕜 := ℂ) v (∇₋ g u) := by
    intro v
    -- `D₋` congruence, then bridge with Riesz
    have := congrArg (fun L : H →L[ℝ] ℂ => L v)
      (DminusCLM_congr_of_eventuallyEq (H:=H) hf hg h)
    simpa [Dminus_eq_inner_gradMinus] using this
  -- Convert to left-inners via conjugation and conclude by `(toDual).symm`.
  have h_left :
      (InnerProductSpace.toDual ℂ H) (∇₋ (H:=H) f u)
        = (InnerProductSpace.toDual ℂ H) (∇₋ g u) := by
    ext v
    have := congrArg star (h_right v)
    simpa [inner_conj_symm] using this
  simpa [gradMinus] using
    congrArg (fun Φ => (InnerProductSpace.toDual ℂ H).symm Φ) h_left

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
  have h1 : D 1 = dz f u + dzbar f u := by
    simpa [dz, dzbar] using
      (show D 1 = DplusCLM (H:=ℂ) (W:=ℂ) f u 1 + DminusCLM (H:=ℂ) (W:=ℂ) f u 1 from
        R_split_point (H:=ℂ) (W:=ℂ) (f:=f) (u:=u) (v:=1))
  have hI : D I = I * dz f u - I * dzbar f u := by
    have hplus : DplusCLM (H:=ℂ) (W:=ℂ) f u (I • (1:ℂ)) = I * DplusCLM (H:=ℂ) (W:=ℂ) f u 1 := by
      simpa [Jc_apply, smul_eq_mul] using
        (Dplus_comm_J_point (H:=ℂ) (W:=ℂ) (f:=f) (u:=u) (v:=1))
    have hminus : DminusCLM (H:=ℂ) (W:=ℂ) f u (I • (1:ℂ)) = - I * DminusCLM (H:=ℂ) (W:=ℂ) f u 1 := by
      simpa [Jc_apply, smul_eq_mul] using
        (Dminus_anticomm_J_point (H:=ℂ) (W:=ℂ) (f:=f) (u:=u) (v:=1))
    have : D I = DplusCLM (H:=ℂ) (W:=ℂ) f u I + DminusCLM (H:=ℂ) (W:=ℂ) f u I :=
      R_split_point (H:=ℂ) (W:=ℂ) (f:=f) (u:=u) (v:=I)
    simpa [dz, dzbar, smul_eq_mul, sub_eq_add_neg] using
      this.trans (by simpa [smul_eq_mul] using congrArg (HAdd.hAdd · ·) hplus hminus)
  -- real/imag decomposition of `w`
  have hw : w = (w.re : ℂ) * 1 + (w.im : ℂ) * I := by
    -- from `re_add_im`: `w = w.re + w.im*I`
    simpa [mul_comm, mul_left_comm, mul_assoc, smul_eq_mul] using (re_add_im w)
  -- compute `D w` via ℝ-linearity:
  calc
    D w
        = D ((w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • I) := by
            simpa [hw, smul_eq_mul]
    _   = (w.re : ℝ) • D 1 + (w.im : ℝ) • D I := by
            simpa [map_add]     -- `map_smul` is simp for CLM over ℝ
    _   = (w.re : ℂ) * (dz f u + dzbar f u)
          + (w.im : ℂ) * (I * dz f u - I * dzbar f u) := by
            simpa [smul_eq_mul, h1, hI]
    _   = (dz f u) * ((w.re : ℂ) + (w.im : ℂ) * I)
          + (dzbar f u) * ((w.re : ℂ) - (w.im : ℂ) * I) := by
            ring
    _   = dz f u * w + dzbar f u * star w := by
            -- `w = re + im*I`, `star w = re - im*I`
            simpa [Complex.re_add_im w, star_eq_re_sub_im w, mul_add, add_mul,
                   sub_eq, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  where
    sub_eq {a b c d} : a * (b - c) + d * (b - -c) = a*b - a*c + d*b - d*(-c) := by ring

end partials_on_C

end scalar_rules
end Wirtinger
