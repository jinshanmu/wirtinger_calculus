import Mathlib

/-!
# Basic.lean — Setup, Notation, and Differentials (single-namespace)

This file provides:

* Complex structure `J` as an `ℝ`-linear map (multiplication by `i`)
* Shorthands `J_H`, `J_W`
* Sandwich `𝒜 T = J_W ∘ T ∘ J_H` on `ℝ`-linear maps
* Wirtinger split on `ℝ`-linear maps: `Tplus`, `Tminus`, and the split lemma
* Predicates `IsCLinearR` / `IsALinearR`
* Hermitian adjoint notation `†` for **complex** continuous linear maps
* Abstract `Conjugation` (ℝ`-linear involution anti-commuting with `J`)
* “Adjoint” construction for **conjugate-linear** (anti-linear) maps via `conjAdjoint`

**New in this merged file:**

* Real Fréchet derivative over `ℝ` on complex pre-Hilbert spaces:
  - `HasRDerivAt`, `fderivR`
  - `Jc` : `J` as a **continuous** `ℝ`-linear map
  - `Aℒ` : sandwich on `H →L[ℝ] W`
  - `DplusCLM` / `DminusCLM` and the split lemma
  - (Anti)commutation of the split with `Jc`
* **Wirtinger gradients** `gradPlus` (∇₊) and `gradMinus` (∇₋) for `f : H → ℂ`
  via the Riesz representation theorem.
* Properties of conjugations, including `Isometry`.

**Convention (mathlib):** the inner product is conjugate-linear in the **first** slot
and linear in the **second** slot. With this convention, for `A : H →L[ℂ] W` one has
`⟪x, A y⟫ = ⟪A† x, y⟫` (equivalently, `⟪A x, y⟫ = ⟪x, A† y⟫`).
For **anti-linear** maps we do *not* overload `†`; instead we provide `conjAdjoint`
with the Riesz identity below.
-/

noncomputable section
open Complex

namespace Wirtinger

/-! # Part I. Basic linear-analytic setup -/

universe u v
variable {H : Type u} {W : Type v}
variable [AddCommGroup H] [Module ℂ H]
variable [AddCommGroup W] [Module ℂ W]

/-! ## Complex structure as an ℝ-linear map: `J` -/

/-- Multiplication by `i` on `V` as an `ℝ`-linear map. -/
@[simp] def J (V : Type _) [AddCommGroup V] [Module ℂ V] : V →ₗ[ℝ] V where
  toFun := fun v => (I : ℂ) • v
  map_add' := by intro v w; simp [smul_add]
  map_smul' := by
    intro r v
    -- real and complex scalars commute on a complex vector space
    simpa using (smul_comm (r : ℝ) (I : ℂ) v).symm

@[simp] lemma J_apply {V} [AddCommGroup V] [Module ℂ V] (v : V) :
    J V v = (I : ℂ) • v := rfl

/-- `J ∘ J = - id` as `ℝ`-linear maps. -/
lemma J_comp_J (V : Type _) [AddCommGroup V] [Module ℂ V] :
    (J V).comp (J V) = - LinearMap.id := by
  ext v; simp [J, smul_smul, Complex.I_mul_I]

/-- PDF-style shorthands. -/
abbrev J_H : H →ₗ[ℝ] H := J H
abbrev J_W : W →ₗ[ℝ] W := J W

/-! ## Sandwich and Wirtinger split on ℝ-linear maps

`𝒜` is an involution on the space of `ℝ`-linear maps: `𝒜 (𝒜 T) = T`.
Its `+1`-eigenspace consists of anti-linear maps (anti-commuting with `J`),
and its `-1`-eigenspace consists of complex-linear maps (commuting with `J`).
The projections are `Tplus = (Id - 𝒜)/2` (complex-linear part) and
`Tminus = (Id + 𝒜)/2` (anti-linear part).
-/

/-- Sandwich operator: `𝒜 T = J_W ∘ T ∘ J_H`. -/
@[simp] def 𝒜 (T : H →ₗ[ℝ] W) : H →ₗ[ℝ] W :=
  (J_W).comp (T.comp J_H)

@[simp] lemma 𝒜_apply (T : H →ₗ[ℝ] W) (v : H) :
    𝒜 T v = (I : ℂ) • T ((I : ℂ) • v) := rfl

/-- Plus (complex-linear) part: `Tplus = (1/2) • (T - 𝒜 T)`. -/
@[simp] def Tplus (T : H →ₗ[ℝ] W) : H →ₗ[ℝ] W :=
  ((1/2 : ℝ)) • (T - 𝒜 T)

/-- Minus (conjugate-linear) part: `Tminus = (1/2) • (T + 𝒜 T)`. -/
@[simp] def Tminus (T : H →ₗ[ℝ] W) : H →ₗ[ℝ] W :=
  ((1/2 : ℝ)) • (T + 𝒜 T)

/-- Split identity (as `ℝ`-linear maps): `T = Tplus + Tminus`. -/
@[simp] lemma plus_add_minus (T : H →ₗ[ℝ] W) :
    Tplus T + Tminus T = T := by
  ext v
  simp only [Tplus, Tminus, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.add_apply]
  rw [← smul_add, sub_add_add_cancel, ← two_smul ℝ]
  rw [smul_smul]; norm_num

/-! ## Complex- and conjugate-linearity via `J` (as predicates)

Relative to `J`, commuting means complex-linear, anti-commuting means anti-linear.
-/

/-- A real-linear `T` is complex-linear iff it commutes with `J`. -/
def IsCLinearR (T : H →ₗ[ℝ] W) : Prop :=
  (J_W).comp T = T.comp J_H

/-- A real-linear `T` is conjugate-linear iff it anti-commutes with `J`. -/
def IsALinearR (T : H →ₗ[ℝ] W) : Prop :=
  (J_W).comp T = - (T.comp J_H)

/-! ## Hermitian adjoint notation for complex continuous linear maps

`A†` denotes `ContinuousLinearMap.adjoint A` and satisfies
`⟪x, A y⟫ = ⟪A† x, y⟫` under mathlib’s convention
(first slot conjugate-linear, second slot linear).
Equivalently, `⟪A x, y⟫ = ⟪x, A† y⟫`.
We **do not** use `†` for anti-linear maps; see `ConjAdj` below.
-/

notation A "†" => ContinuousLinearMap.adjoint A

/-! ## Conjugations (abstract)

A conjugation is an `ℝ`-linear involution that anti-commutes with `J`.
When an inner product is present, being “antiunitary” means it preserves the inner product
up to complex conjugation:
`⟪C x, C y⟫ = star ⟪x, y⟫` (equivalently, `= ⟪y, x⟫` by conjugate symmetry).
-/

structure Conjugation (V : Type _) [AddCommGroup V] [Module ℂ V] where
  C : V →ₗ[ℝ] V
  involutive : C.comp C = LinearMap.id
  antiJ : C.comp (J V) = - (J V).comp C

section
variable {V : Type _} [AddCommGroup V] [Module ℂ V]

@[simp] lemma Conjugation.comp_self_id (C : Conjugation V) :
    C.C.comp C.C = LinearMap.id := C.involutive

/-- Pointwise form of `C ∘ J = - J ∘ C`. -/
@[simp] lemma Conjugation.antiJ_apply (C : Conjugation V) (v : V) :
    C.C ((I : ℂ) • v) = - (I : ℂ) • C.C v := by
  have := congrArg (fun (L : V →ₗ[ℝ] V) => L v) C.antiJ
  simpa [LinearMap.comp_apply, J, smul_smul] using this
end

/-! ## Conjugations as antiunitaries (with inner product) -/
section
-- Keep algebraic + analytic instances explicit to satisfy all downstream lemmas.
variable {V : Type _}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A conjugation is *antiunitary* if it preserves inner products up to complex
conjugation: `⟪C x, C y⟫ = star ⟪x, y⟫`. With mathlib’s convention this is
equivalent to `⟪C x, C y⟫ = ⟪y, x⟫`. -/
def Conjugation.IsAntiunitary (C : Conjugation V) : Prop :=
  ∀ x y : V, inner (𝕜 := ℂ) (C.C x) (C.C y) = star (inner (𝕜 := ℂ) x y)

/-- Direct statement of antiunitarity. -/
@[simp] lemma Conjugation.inner_conj_conj
    (C : Conjugation V) (hC : C.IsAntiunitary) (x y : V) :
    inner (𝕜 := ℂ) (C.C x) (C.C y) = star (inner (𝕜 := ℂ) x y) :=
  hC x y

/-- Swapped form via conjugate symmetry: `⟪C x, C y⟫ = ⟪y, x⟫`. -/
@[simp] lemma Conjugation.inner_conj_conj_swap
    (C : Conjugation V) (hC : C.IsAntiunitary) (x y : V) :
    inner (𝕜 := ℂ) (C.C x) (C.C y) = inner (𝕜 := ℂ) y x := by
  classical
  have h1 : inner (𝕜 := ℂ) (C.C x) (C.C y) = star (inner (𝕜 := ℂ) x y) := hC x y
  have h2 : star (inner (𝕜 := ℂ) x y) = inner (𝕜 := ℂ) y x := by
    change (starRingEnd ℂ) (inner (𝕜 := ℂ) x y) = inner (𝕜 := ℂ) y x
    exact inner_conj_symm (𝕜 := ℂ) y x
  exact h1.trans h2

/-- An antiunitary conjugation is an isometry. -/
lemma Conjugation.isometry (C : Conjugation V) (hC : C.IsAntiunitary) : Isometry C.C := by
  -- Show distances are preserved.
  refine Isometry.of_dist_eq (fun x y => ?_)
  -- First, show squared norms are preserved.
  have h_norm_sq : ∀ v, ‖C.C v‖^2 = ‖v‖^2 := by
    intro v
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), Conjugation.inner_conj_conj C hC v v, star_re,
        ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  -- Apply to x - y and take sqrt.
  have hsq := congrArg Real.sqrt (h_norm_sq (x - y))
  simpa [dist_eq_norm, map_sub, Real.sqrt_sq_eq_abs,
         abs_of_nonneg (norm_nonneg _)] using hsq

end

/-! ## Conjugate-linear (anti-linear) maps packaged as `ℝ`-linear with `antiJ`

`ALinear` records real-linearity together with anti-commutation with `J`.
(Continuity is not assumed here; add it separately when needed.)
-/

structure ALinear
  (H : Type u) (W : Type v)
  [AddCommGroup H] [Module ℂ H]
  [AddCommGroup W] [Module ℂ W] where
  toLinear : H →ₗ[ℝ] W
  antiJ : (J W).comp toLinear = - toLinear.comp (J H)

namespace ALinear

@[simp] lemma antiJ_apply
  {H : Type u} {W : Type v}
  [AddCommGroup H] [Module ℂ H]
  [AddCommGroup W] [Module ℂ W]
  (T : ALinear H W) (v : H) :
  (I : ℂ) • T.toLinear v = - T.toLinear ((I : ℂ) • v) := by
  have := congrArg (fun (L : H →ₗ[ℝ] W) => L v) T.antiJ
  simpa [LinearMap.comp_apply, J, smul_smul] using this

/-- `ALinear` implies the commutation predicate `IsALinearR`. -/
lemma isALinearR
  {H : Type u} {W : Type v}
  [AddCommGroup H] [Module ℂ H]
  [AddCommGroup W] [Module ℂ W]
  (T : ALinear H W) :
  IsALinearR (T := T.toLinear) := T.antiJ

end ALinear

end Wirtinger

/-! ## Inner product identities (conjugate symmetry)

With mathlib’s convention (first slot conjugate-linear), conjugate symmetry reads
`star ⟪x, y⟫ = ⟪y, x⟫`. Equivalently, `⟪x, y⟫ = star ⟪y, x⟫`.
-/

section
variable {H : Type _}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Conjugate symmetry in `star` form. -/
@[simp] lemma inner_star_eq_swap (x y : H) :
    star (inner (𝕜 := ℂ) x y) = inner (𝕜 := ℂ) y x := by
  classical
  change (starRingEnd ℂ) (inner (𝕜 := ℂ) x y) = inner (𝕜 := ℂ) y x
  exact inner_conj_symm (𝕜 := ℂ) y x

end

/-!
# Differentials (real Fréchet derivative and Wirtinger split)

We work with continuous `ℝ`-linear maps (`→L[ℝ]`) and the real Fréchet
derivative `fderiv ℝ`. We lift `J` to a continuous map `Jc`, define the
sandwich `Aℒ` on `→L[ℝ]`, and perform the Wirtinger split.
-/

namespace Wirtinger

universe u v

-- This section assumes a pre-Hilbert space structure. Completeness is not required
-- for these definitions, only for deeper theorems or the adjoint construction.
variable {H : Type u} {W : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-! ## Real Fréchet derivative -/

abbrev HasRDerivAt (f : H → W) (u : H) (D : H →L[ℝ] W) : Prop :=
  HasFDerivAt f D u

@[simp] abbrev fderivR (f : H → W) (u : H) : H →L[ℝ] W :=
  fderiv ℝ f u

/-! ## `J` as a continuous `ℝ`-linear map -/

/-- `Jc V` is multiplication by `I` as a *continuous* `ℝ`-linear map. -/
def Jc (V : Type _) [NormedAddCommGroup V] [NormedSpace ℂ V] : V →L[ℝ] V :=
  { toLinearMap := J V,
    cont := continuous_const_smul (I : ℂ) }

@[simp] lemma Jc_apply {V} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) :
    Jc V v = (I : ℂ) • v := rfl

/-- Pointwise form of `Jc ∘ Jc = -id`. -/
@[simp] lemma Jc_comp_Jc_apply (V : Type _) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (v : V) :
    ((Jc V).comp (Jc V)) v = - v := by
  simp [ContinuousLinearMap.comp_apply, Jc_apply, smul_smul, Complex.I_mul_I]

/-- Shorthands for `Jc` on domain/codomain. -/
abbrev Jc_H : H →L[ℝ] H := Jc H
abbrev Jc_W : W →L[ℝ] W := Jc W

/-! ## Sandwich on continuous `ℝ`-linear maps -/

/-- Sandwich operator on `H →L[ℝ] W`: `Aℒ T = Jc_W ∘ T ∘ Jc_H`. -/
@[simp] def Aℒ (T : H →L[ℝ] W) : H →L[ℝ] W :=
  (Jc_W).comp (T.comp Jc_H)

@[simp] lemma Aℒ_apply (T : H →L[ℝ] W) (v : H) :
    Aℒ (H:=H) (W:=W) T v = (I : ℂ) • T ((I : ℂ) • v) := by
  simp [Aℒ, ContinuousLinearMap.comp_apply, Jc_apply]

/-- `Aℒ` is an involution: `Aℒ (Aℒ T) = T`. -/
lemma Aℒ_involutive (T : H →L[ℝ] W) :
    Aℒ (H:=H) (W:=W) (Aℒ T) = T := by
  ext v
  simp [Aℒ, Jc_apply, ContinuousLinearMap.comp_apply, smul_smul, Complex.I_mul_I]

/-! ## Wirtinger split of the real Fréchet derivative -/

/-- Plus (complex-linear) part. -/
def DplusCLM (f : H → W) (u : H) : H →L[ℝ] W :=
  ((1/2 : ℝ)) • (fderivR f u - Aℒ (H:=H) (W:=W) (fderivR f u))

/-- Minus (conjugate-linear) part. -/
def DminusCLM (f : H → W) (u : H) : H →L[ℝ] W :=
  ((1/2 : ℝ)) • (fderivR f u + Aℒ (H:=H) (W:=W) (fderivR f u))

/-- Split identity: `Df = Dplus + Dminus`. -/
lemma Dplus_add_Dminus (f : H → W) (u : H) :
    DplusCLM (H:=H) (W:=W) f u + DminusCLM f u = fderivR f u := by
  ext v
  simp only [DplusCLM, DminusCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  rw [← smul_add, sub_add_add_cancel, ← two_smul ℝ]
  rw [smul_smul]; norm_num

/-! ## (Anti)commutation with `Jc` (direction linearity) -/

/-- `Dplus` commutes with `Jc`: complex-linear in the direction. -/
lemma isCLinearR_Dplus (f : H → W) (u : H) :
    (Jc_W).comp (DplusCLM f u) = (DplusCLM f u).comp (Jc_H) := by
  let D := fderivR f u
  simp_rw [DplusCLM, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
           ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  apply congr_arg ((1/2 : ℝ) • ·)
  have h1 : Jc_W.comp (Aℒ D) = -D.comp Jc_H := by
    ext x
    change Jc_W (Aℒ D x) = -(D (Jc_H x))
    rw [Aℒ_apply, Jc_apply, Jc_apply, smul_smul, I_mul_I, neg_one_smul]
  have h2 : (Aℒ D).comp Jc_H = -Jc_W.comp D := by
    ext x
    change Aℒ D (Jc_H x) = - (Jc_W (D x))
    rw [Aℒ_apply, Jc_apply, Jc_apply, smul_smul, I_mul_I, neg_one_smul, D.map_neg, smul_neg]
  rw [h1, h2, sub_neg_eq_add, sub_neg_eq_add, add_comm]

/-- `Dminus` anti-commutes with `Jc`: conjugate-linear in the direction. -/
lemma isALinearR_Dminus (f : H → W) (u : H) :
    (Jc_W).comp (DminusCLM f u) = - (DminusCLM f u).comp (Jc_H) := by
  let D := fderivR f u
  simp_rw [DminusCLM]
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, ←smul_neg]
  apply congr_arg ((1/2 : ℝ) • ·)
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, neg_add_rev]
  have h1 : Jc_W.comp (Aℒ D) = -D.comp Jc_H := by
    ext x
    change Jc_W (Aℒ D x) = -(D (Jc_H x))
    rw [Aℒ_apply, Jc_apply, Jc_apply, smul_smul, I_mul_I, neg_one_smul]
  have h2 : (Aℒ D).comp Jc_H = -Jc_W.comp D := by
    ext x
    change Aℒ D (Jc_H x) = - (Jc_W (D x))
    rw [Aℒ_apply, Jc_apply, Jc_apply, smul_smul, I_mul_I, neg_one_smul, D.map_neg, smul_neg]
  rw [h1, h2]; abel

/-- Pointwise decomposition of the real Gâteaux derivative. -/
lemma fderivR_apply_split (f : H → W) (u v : H) :
    fderivR f u v = DplusCLM f u v + DminusCLM f u v := by
  simpa using
    (congrArg (fun (T : H →L[ℝ] W) => T v) (Dplus_add_Dminus (H:=H) (W:=W) f u)).symm

end Wirtinger

/-! # Wirtinger Gradients (via Riesz Representation)

For a scalar-valued function `f : H → ℂ`, we can use the Riesz representation
theorem to find unique vectors `∇₊f[u]` and `∇₋f[u]` in `H` that represent
the action of the Wirtinger derivatives `D₊f[u]` and `D₋f[u]`.
This requires `H` to be a complete inner product space (a Hilbert space).
-/
namespace Wirtinger

universe u
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The complex-linear part `DplusCLM` of the derivative of `f : H → ℂ` is a
continuous ℂ-linear map, i.e., a bounded linear functional. -/
def DplusCLM_c_linear (f : H → ℂ) (u : H) : H →L[ℂ] ℂ :=
{ toLinearMap :=
  { toFun := fun v => DplusCLM (H:=H) (W:=ℂ) f u v
    , map_add' := by intro x y; simp
    , map_smul' := by
        intro c v
        set D := DplusCLM (H:=H) (W:=ℂ) f u
        have hJ : D (I • v) = I • D v := by
          have := congrArg (fun (L : H →L[ℝ] ℂ) => L v)
                    (isCLinearR_Dplus (H:=H) (W:=ℂ) f u)
          simpa [Jc_apply, ContinuousLinearMap.comp_apply] using this.symm
        -- Decompose c • v using its real and imaginary parts, then apply the ℝ-linear map D.
        -- Use D's C-linearity (hJ) to reconstruct the complex scalar multiplication.
        calc D (c • v)
          _ = D (c.re • v + c.im • (I • v)) := by rw [Complex.smul_def]
          _ = D (c.re • v) + D (c.im • (I • v)) := by rw [D.map_add]
          _ = c.re • D v + c.im • D (I • v) := by rw [D.map_smul, D.map_smul]
          _ = c.re • D v + c.im • (I • D v) := by rw [hJ]
          _ = c • D v := by rw [Complex.smul_def]
  }
  , cont := (DplusCLM (H:=H) (W:=ℂ) f u).continuous
}

/-- The Wirtinger gradient `∇₊f[u]` (or `gradPlus f u`).
This is the vector in `H` representing `D₊f` via the Riesz theorem. -/
def gradPlus (f : H → ℂ) (u : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (DplusCLM_c_linear f u)

/-- The defining property of `gradPlus`: `D₊f[u][v] = ⟪∇₊f[u], v⟫`. -/
@[simp] lemma inner_gradPlus_eq_Dplus (f : H → ℂ) (u v : H) :
    inner (𝕜 := ℂ) (gradPlus f u) v = DplusCLM (H:=H) (W:=ℂ) f u v := by
  change ((InnerProductSpace.toDual ℂ H) (gradPlus f u)) v
          = DplusCLM (H:=H) (W:=ℂ) f u v
  simp [gradPlus, DplusCLM_c_linear]

/-- The map `v ↦ star (DminusCLM f u v)` is a continuous ℂ-linear functional.
This is a helper to define `gradMinus` using the Riesz theorem, which applies
to linear (not conjugate-linear) functionals. -/
def DminusCLM_star_c_linear (f : H → ℂ) (u : H) : H →L[ℂ] ℂ :=
{ toFun := fun v => star (DminusCLM (H:=H) (W:=ℂ) f u v)
  , map_add' := by intro x y; simp [star_add]
  , map_smul' := by
      intro c v
      set D := DminusCLM (H:=H) (W:=ℂ) f u
      have hJ : D (I • v) = -I • D v := by
        have h := congrArg (fun (L : H →L[ℝ] ℂ) => L v) (isALinearR_Dminus (H:=H) (W:=ℂ) f u)
        simpa [Jc_apply, ContinuousLinearMap.comp_apply, neg_eq_iff_eq_neg] using h.symm
      -- Goal: star (D (c • v)) = c • star (D v)
      calc star (D (c • v))
        _ = star (D (c.re • v + c.im • (I • v))) := by rw [Complex.smul_def]
        _ = star (c.re • D v + c.im • D (I • v)) := by rw [D.map_add, D.map_smul, D.map_smul]
        _ = star (c.re • D v) + star (c.im • D (I • v)) := by rw [star_add]
        _ = c.re • star (D v) + c.im • star (D (I • v)) := by rw [star_smul, star_smul]
        _ = c.re • star (D v) + c.im • star (-I • D v) := by rw [hJ]
        _ = c.re • star (D v) + c.im • (-star I • star (D v)) := by rw [star_neg, star_mul]
        _ = c.re • star (D v) + c.im • (I • star (D v)) := by rw [star_I, neg_neg]
        _ = c • star (D v) := by rw [Complex.smul_def]
  , cont := (continuous_star.comp (DminusCLM (H:=H) (W:=ℂ) f u).continuous)
}

/-- The Wirtinger gradient `∇₋f[u]` (or `gradMinus f u`).
`D₋f` is conjugate-linear, so we represent it via `D₋f[u][v] = ⟪v, ∇₋f[u]⟫`.
This is equivalent to `star (D₋f[u][v]) = ⟪∇₋f[u], v⟫`, so we apply Riesz to
the ℂ-linear functional `v ↦ star (D₋f[u][v])`. -/
def gradMinus (f : H → ℂ) (u : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (DminusCLM_star_c_linear f u)

/-- The defining property of `gradMinus`: `D₋f[u][v] = ⟪v, ∇₋f[u]⟫`. -/
@[simp] lemma Dminus_eq_inner_gradMinus (f : H → ℂ) (u v : H) :
    DminusCLM (H:=H) (W:=ℂ) f u v = inner (𝕜 := ℂ) v (gradMinus f u) := by
  have h : inner (𝕜 := ℂ) (gradMinus f u) v
            = star (DminusCLM (H:=H) (W:=ℂ) f u v) := by
    change ((InnerProductSpace.toDual ℂ H) (gradMinus f u)) v
            = star (DminusCLM (H:=H) (W:=ℂ) f u v)
    simp [gradMinus, DminusCLM_star_c_linear]
  have := congrArg star h
  simpa [inner_star_eq_swap] using this.symm

/-- The Wirtinger split of the real Gâteaux derivative in terms of the gradients. -/
lemma fderivR_apply_split_grad (f : H → ℂ) (u v : H) :
    fderivR (H:=H) (W:=ℂ) f u v
      = inner (𝕜 := ℂ) (gradPlus f u) v + inner (𝕜 := ℂ) v (gradMinus f u) := by
  simpa [inner_gradPlus_eq_Dplus, Dminus_eq_inner_gradMinus] using
    (fderivR_apply_split (H:=H) (W:=ℂ) f u v)

end Wirtinger

/-!
## Hermitian “adjoint” for a conjugate-linear map

**Setup.** `inner` is conjugate-linear in the first slot and linear in the second
(mathlib).  Given a **conjugate-linear** map `B : E → F`
(i.e. `B (a • y) = (star a) • B y`) that is additive and continuous, we define
`(conjAdjoint B) : F → E` via the Riesz representation so that:

* `⟪(conjAdjoint B) x, y⟫ = ⟪B y, x⟫` for all `x : F`, `y : E`;
* equivalently (by conjugate symmetry), `⟪x, B y⟫ = star ⟪(conjAdjoint B) x, y⟫`.

**Remark.** Because the first slot of `inner` is conjugate-linear while `B` is
conjugate-linear, the map `y ↦ ⟪B y, x⟫` is ℂ-linear in `y`
(conjugation twice gives linearity).
-/

namespace ConjAdj

/-- For fixed `x : F`, the bounded **ℂ-linear** functional `y ↦ ⟪B y, x⟫`.
Linearity in `y` holds because `B` is conjugate-linear and the inner product is
conjugate-linear in its first slot. -/
private def phi
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (B : E → F)
  (h_add : ∀ y z, B (y + z) = B y + B z)
  (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
  (h_cont : Continuous B)
  (x : F) : E →L[ℂ] ℂ :=
by
  classical
  -- 1) Underlying linear map (ℂ-linear in `y` since `B` and the first slot are
  -- both conjugate-linear):
  let L : E →ₗ[ℂ] ℂ :=
  { toFun := fun y => inner (𝕜 := ℂ) (B y) x
  , map_add' := by
      intro y z
      simp [h_add y z]
  , map_smul' := by
      intro a y
      -- `B (a•y) = star a • B y`; first slot is conjugate-linear:
      -- `⟪(star a) • B y, x⟫ = a * ⟪B y, x⟫`.
      simp [h_smul a y, mul_comm] }
  -- 2) Continuity: `y ↦ ⟪B y, x⟫ = star ⟪x, B y⟫` is continuous as a composition.
  have hx : Continuous fun w : F =>
      ((InnerProductSpace.toDual ℂ F) x) w :=
    ((InnerProductSpace.toDual ℂ F) x).continuous
  have hcomp : Continuous fun y : E =>
      ((InnerProductSpace.toDual ℂ F) x) (B y) := hx.comp h_cont
  have hstar : Continuous fun y : E =>
      star (inner (𝕜 := ℂ) x (B y)) :=
    continuous_star.comp hcomp
  have hLcont : Continuous fun y : E => L y := by
    -- Convert `hstar` to the goal using conjugate symmetry.
    convert hstar using 1
    ext y; simp [L]
  -- 3) Package:
  exact { toLinearMap := L, cont := hLcont }

/-- Adjoint of a conjugate-linear `B`, via the Riesz isometry
(notated `conjAdjoint`, not `†`). -/
def conjAdjoint
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (B : E → F)
  (h_add : ∀ y z, B (y + z) = B y + B z)
  (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
  (h_cont : Continuous B) :
  F → E :=
fun x => (InnerProductSpace.toDual ℂ E).symm (phi B h_add h_smul h_cont x)

/-- Riesz characterization for the conjugate-linear adjoint:
`⟪(conjAdjoint B) x, y⟫ = ⟪B y, x⟫`. -/
lemma inner_conjAdjoint
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (B : E → F)
  (h_add : ∀ y z, B (y + z) = B y + B z)
  (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
  (h_cont : Continuous B)
  (x : F) (y : E) :
  inner (𝕜 := ℂ) ((conjAdjoint B h_add h_smul h_cont) x) y
  = inner (𝕜 := ℂ) (B y) x :=
by
  classical
  change
    (InnerProductSpace.toDual ℂ E) ((conjAdjoint B h_add h_smul h_cont) x) y
    = inner (𝕜 := ℂ) (B y) x
  simp [conjAdjoint, phi]

/-- “Flipped” form of the same identity:
`⟪x, B y⟫ = star ⟪(conjAdjoint B) x, y⟫`. -/
lemma inner_eq_star_adjoint
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (B : E → F)
  (h_add : ∀ y z, B (y + z) = B y + B z)
  (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
  (h_cont : Continuous B)
  (x : F) (y : E) :
  inner (𝕜 := ℂ) x (B y) =
  star (inner (𝕜 := ℂ) ((conjAdjoint B h_add h_smul h_cont) x) y) :=
by
  classical
  have h := inner_conjAdjoint B h_add h_smul h_cont x y
  -- Take star and use conjugate symmetry:
  simpa [inner_conj_symm] using (congrArg star h).symm

end ConjAdj
