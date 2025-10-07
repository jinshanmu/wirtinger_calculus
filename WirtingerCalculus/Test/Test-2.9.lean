import Mathlib

/-
# Basic.lean — Setup, Notation, and Differentials (single-namespace)

This file provides:

* Complex structure `J` as an `ℝ`-linear map (multiplication by `i`)
* Shorthands `J_H`, `J_W`
* Sandwich `𝒜 T = J_W ∘ T ∘ J_H` on `ℝ`-linear maps
* Wirtinger split on `ℝ`-linear maps: `Tplus`, `Tminus`, and the split lemma
* Predicates `IsCLinearR` / `IsALinearR`
* Hermitian adjoint notation `†` for complex continuous linear maps
* Abstract `Conjugation` (`ℝ`-linear involution anti-commuting with `J`)
* “Adjoint” construction for conjugate-linear maps via `conjAdjoint`

New in this merged file:

* Real Fréchet derivative over `ℝ` on complex pre-Hilbert spaces:
  - `HasRDerivAt`, `fderivR`
  - `Jc` as a continuous `ℝ`-linear map
  - `Aℒ` sandwich on `H →L[ℝ] W`
  - `DplusCLM` / `DminusCLM` and the split lemma
  - (Anti)commutation of the split with `Jc`

Convention (mathlib): the inner product is conjugate-linear in the first slot
and linear in the second slot. With this convention, for `A : H →L[ℂ] W` one has
`⟪x, A y⟫ = ⟪A† x, y⟫` (equivalently, `⟪A x, y⟫ = ⟪x, A† y⟫`).
For anti-linear maps we do not overload `†`; instead we provide `conjAdjoint`.
-/

noncomputable section
open Complex

namespace Wirtinger

-- Part I. Basic linear-analytic setup

universe u v
variable {H : Type u} {W : Type v}
variable [AddCommGroup H] [Module ℂ H]
variable [AddCommGroup W] [Module ℂ W]

/- Complex structure as an ℝ-linear map: `J` -/

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

/- Sandwich and Wirtinger split on ℝ-linear maps -/

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

/- Complex- and conjugate-linearity via `J` (as predicates) -/

/-- A real-linear `T` is complex-linear iff it commutes with `J`. -/
def IsCLinearR (T : H →ₗ[ℝ] W) : Prop :=
  (J_W).comp T = T.comp J_H

/-- A real-linear `T` is conjugate-linear iff it anti-commutes with `J`. -/
def IsALinearR (T : H →ₗ[ℝ] W) : Prop :=
  (J_W).comp T = - (T.comp J_H)

/- Hermitian adjoint notation for complex continuous linear maps -/

notation A "†" => ContinuousLinearMap.adjoint A

/- Conjugations (abstract) -/

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
  have h := congrArg (fun (L : V →ₗ[ℝ] V) => L v) C.antiJ
  -- normalize so RHS is `-I • _`
  simpa [LinearMap.comp_apply, J, smul_smul, neg_smul] using h
end

/- Conjugations with inner product -/
section
variable {V : Type _}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A conjugation is antiunitary if it preserves inner products up to conjugation. -/
def Conjugation.IsAntiunitary (C : Conjugation V) : Prop :=
  ∀ x y : V, inner (𝕜 := ℂ) (C.C x) (C.C y) = star (inner (𝕜 := ℂ) x y)

@[simp] lemma Conjugation.inner_conj_conj
    (C : Conjugation V) (hC : C.IsAntiunitary) (x y : V) :
    inner (𝕜 := ℂ) (C.C x) (C.C y) = star (inner (𝕜 := ℂ) x y) :=
  hC x y

@[simp] lemma Conjugation.inner_conj_conj_swap
    (C : Conjugation V) (hC : C.IsAntiunitary) (x y : V) :
    inner (𝕜 := ℂ) (C.C x) (C.C y) = inner (𝕜 := ℂ) y x := by
  simp [hC]

end

end Wirtinger

/- Inner product identities (conjugate symmetry) -/

section
variable {H : Type _}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Conjugate symmetry in `star` form. -/
@[simp] lemma inner_star_eq_swap (x y : H) :
    star (inner (𝕜 := ℂ) x y) = inner (𝕜 := ℂ) y x := by
  simp

end

/- Differentials (real Fréchet derivative and Wirtinger split) -/

namespace Wirtinger

universe u v

variable {H : Type u} {W : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/- Real Fréchet derivative -/

abbrev HasRDerivAt (f : H → W) (u : H) (D : H →L[ℝ] W) : Prop :=
  HasFDerivAt f D u

@[simp] abbrev fderivR (f : H → W) (u : H) : H →L[ℝ] W :=
  fderiv ℝ f u

/- `J` as a continuous `ℝ`-linear map -/

/-- `Jc V` is multiplication by `I` as a continuous `ℝ`-linear map. -/
def Jc (V : Type _) [NormedAddCommGroup V] [NormedSpace ℂ V] : V →L[ℝ] V :=
  { toLinearMap := J V,
    cont := continuous_const_smul (I : ℂ) }

@[simp] lemma Jc_apply {V} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) :
    Jc V v = (I : ℂ) • v := rfl

@[simp] lemma Jc_comp_Jc_apply (V : Type _) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (v : V) :
    ((Jc V).comp (Jc V)) v = - v := by
  simp [ContinuousLinearMap.comp_apply, Jc_apply, smul_smul, Complex.I_mul_I]

abbrev Jc_H : H →L[ℝ] H := Jc H
abbrev Jc_W : W →L[ℝ] W := Jc W

/- Sandwich on continuous `ℝ`-linear maps -/

/-- `Aℒ T = Jc_W ∘ T ∘ Jc_H`. -/
@[simp] def Aℒ (T : H →L[ℝ] W) : H →L[ℝ] W :=
  (Jc_W).comp (T.comp Jc_H)

@[simp] lemma Aℒ_apply (T : H →L[ℝ] W) (v : H) :
    Aℒ (H:=H) (W:=W) T v = (I : ℂ) • T ((I : ℂ) • v) := by
  simp [Aℒ, ContinuousLinearMap.comp_apply, Jc_apply]

lemma Aℒ_involutive (T : H →L[ℝ] W) :
    Aℒ (H:=H) (W:=W) (Aℒ T) = T := by
  ext v
  simp [Aℒ, Jc_apply, ContinuousLinearMap.comp_apply, smul_smul, Complex.I_mul_I]

/- Wirtinger split of the real Fréchet derivative -/

/-- Plus (complex-linear) part. -/
def DplusCLM (f : H → W) (u : H) : H →L[ℝ] W :=
  ((1/2 : ℝ)) • (fderivR f u - Aℒ (H:=H) (W:=W) (fderivR f u))

/-- Minus (conjugate-linear) part. -/
def DminusCLM (f : H → W) (u : H) : H →L[ℝ] W :=
  ((1/2 : ℝ)) • (fderivR f u + Aℒ (H:=H) (W:=W) (fderivR f u))

lemma Dplus_add_Dminus (f : H → W) (u : H) :
    DplusCLM (H:=H) (W:=W) f u + DminusCLM f u = fderivR f u := by
  ext v
  simp only [DplusCLM, DminusCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
  rw [← smul_add, sub_add_add_cancel, ← two_smul ℝ]
  rw [smul_smul]; norm_num

/- (Anti)commutation with `Jc` (direction linearity) -/

lemma isCLinearR_Dplus (f : H → W) (u : H) :
    (Jc_W).comp (DplusCLM f u) = (DplusCLM f u).comp (Jc_H) := by
  let D := fderivR f u
  simp_rw [DplusCLM, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
           ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  apply congr_arg ((1/2 : ℝ) • ·)
  have h1 : Jc_W.comp (Aℒ D) = -D.comp Jc_H := by
    ext x
    change Jc_W (Aℒ D x) = -(D (Jc_H x))
    rw [Aℒ_apply, Jc_apply, Jc_apply, smul_smul, Complex.I_mul_I, neg_one_smul]
  have h2 : (Aℒ D).comp Jc_H = -Jc_W.comp D := by
    ext x
    change Aℒ D (Jc_H x) = - (Jc_W (D x))
    rw [Aℒ_apply, Jc_apply, Jc_apply, smul_smul, Complex.I_mul_I, neg_one_smul, D.map_neg, smul_neg]
  rw [h1, h2, sub_neg_eq_add, sub_neg_eq_add, add_comm]

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
    rw [Aℒ_apply, Jc_apply, Jc_apply, smul_smul, Complex.I_mul_I, neg_one_smul]
  have h2 : (Aℒ D).comp Jc_H = -Jc_W.comp D := by
    ext x
    change Aℒ D (Jc_H x) = - (Jc_W (D x))
    rw [Aℒ_apply, Jc_apply, Jc_apply, smul_smul, Complex.I_mul_I, neg_one_smul, D.map_neg, smul_neg]
  rw [h1, h2]; abel

lemma fderivR_apply_split (f : H → W) (u v : H) :
    fderivR f u v = DplusCLM f u v + DminusCLM f u v := by
  -- Avoid `simpa` to appease the linter: derive equality directly.
  have h := congrArg (fun (T : H →L[ℝ] W) => T v) (Dplus_add_Dminus (H:=H) (W:=W) f u)
  exact h.symm

end Wirtinger

/- Hermitian “adjoint” for a conjugate-linear map -/

namespace ConjAdj

/-- For fixed `x : F`, the bounded ℂ-linear functional `y ↦ ⟪B y, x⟫`. -/
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
  -- Underlying linear map:
  let L : E →ₗ[ℂ] ℂ :=
  { toFun := fun y => inner (𝕜 := ℂ) (B y) x
  , map_add' := by
      intro y z
      rw [h_add, inner_add_left]
  , map_smul' := by
      intro a y
      -- `B (a•y) = star a • B y` and the first slot is conjugate-linear.
      have hb : B (a • y) = (star a) • B y := h_smul a y
      have h' : inner (𝕜 := ℂ) ((star a) • B y) x = a * inner (𝕜 := ℂ) (B y) x := by
        -- ⟪(star a) • u, v⟫ = star (star a) * ⟪u,v⟫ = a * ⟪u,v⟫
        simpa [star_star, mul_comm] using
          (inner_smul_left (𝕜 := ℂ) (x := B y) (y := x) (r := star a))
      simpa [hb] using h' }
  -- Continuity:
  have hx : Continuous fun w : F =>
      ((InnerProductSpace.toDual ℂ F) x) w :=
    ((InnerProductSpace.toDual ℂ F) x).continuous
  have hcomp : Continuous fun y : E =>
      ((InnerProductSpace.toDual ℂ F) x) (B y) := hx.comp h_cont
  have hstar : Continuous fun y : E =>
      star (inner (𝕜 := ℂ) x (B y)) :=
    continuous_star.comp hcomp
  have hLcont : Continuous fun y : E => L y := by
    convert hstar using 1
    ext y; simp only [L]; simp
  -- Package:
  exact { toLinearMap := L, cont := hLcont }

/-- Adjoint of a conjugate-linear `B`, via Riesz. -/
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

/-- Riesz characterization for the conjugate-linear adjoint. -/
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

/-- Flipped form: `⟪x, B y⟫ = star ⟪(conjAdjoint B) x, y⟫`. -/
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
  calc
    inner (𝕜 := ℂ) x (B y) = star (inner (𝕜 := ℂ) (B y) x) := by simp
    _ = star (inner (𝕜 := ℂ) ((conjAdjoint B h_add h_smul h_cont) x) y) :=
        by rw [inner_conjAdjoint]

end ConjAdj

/-!
# Wirtinger Gradients (via Riesz Representation)

For a scalar-valued function `f : H → ℂ`, the complex-linear part `DplusCLM`
acts as a bounded ℂ-linear functional, and the conjugate-linear part `DminusCLM`
becomes ℂ-linear after composing with complex conjugation. We then define
`gradPlus` and `gradMinus` using the Riesz isomorphism.
-/
namespace Wirtinger

universe u
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The complex-linear part `DplusCLM` of the derivative of `f : H → ℂ`
is a continuous ℂ-linear functional. -/
def DplusCLM_c_linear (f : H → ℂ) (u : H) : H →L[ℂ] ℂ :=
{ toLinearMap :=
  { toFun := fun v => DplusCLM (H:=H) (W:=ℂ) f u v
  , map_add' := by intro x y; simp
  , map_smul' := by
      intro a v
      set D := DplusCLM (H:=H) (W:=ℂ) f u
      -- from commutation with J: D (I • v) = I • D v
      have h0 := congrArg (fun (L : H →L[ℝ] ℂ) => L v)
                  (isCLinearR_Dplus (H:=H) (W:=ℂ) f u)
      -- h0 : Jc_ℂ (D v) = D (Jc_H v)
      have hJ : D (I • v) = I • D v := by
        -- rewrite both sides transparently; avoid large `simp`
        have : (Jc ℂ) (D v) = D (Jc_H v) := h0
        -- first replace the right
        have : (Jc ℂ) (D v) = D ((I : ℂ) • v) := by
          simpa [Jc_apply, ContinuousLinearMap.comp_apply] using this
        -- now replace the left
        have : (I : ℂ) • D v = D ((I : ℂ) • v) := by
          simpa [Jc_apply] using this
        exact this.symm
      -- split `a` and push through
      have ha : a = (a.re : ℂ) + (a.im : ℂ) * I := by
        simpa [mul_comm] using (Complex.re_add_im a).symm
      calc
        D (a • v)
            = D (((a.re : ℂ) + (a.im : ℂ) * I) • v) := by simpa [ha]
        _   = D ((a.re : ℂ) • v + ((a.im : ℂ) * I) • v) := by
                simpa [add_smul]
        _   = D ((a.re : ℝ) • v + (a.im : ℝ) • (I • v)) := by
                -- convert each summand to ℝ-smul form (definitional equalities)
                have hA : ((a.re : ℂ) • v) = (a.re : ℝ) • v := rfl
                have hB : (((a.im : ℂ) * I) • v) = (a.im : ℝ) • (I • v) := by
                  -- ((a.im : ℂ) * I) • v = (a.im : ℂ) • (I • v), then view (a.im) as ℝ-scalar
                  -- both steps are defeq
                  simpa [smul_smul]
                simpa [hA, hB]
        _   = D ((a.re : ℝ) • v) + D ((a.im : ℝ) • (I • v)) := by
                simpa using (D.map_add _ _)
        _   = (a.re : ℝ) • D v + (a.im : ℝ) • D (I • v) := by
                simp [D.map_smul]
        _   = (a.re : ℝ) • D v + (a.im : ℝ) • (I • D v) := by
                simpa [hJ]
        _   = a • D v := by
                -- convert ℝ-smul on ℂ to multiplication and recombine
                have : (a.re : ℝ) • D v + (a.im : ℝ) • (I • D v)
                      = ((a.re : ℂ) + (a.im : ℂ) * I) * D v := by
                  -- r•z = (r : ℂ) * z on ℂ
                  simp [Algebra.smul_def, add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc]
                simpa [ha, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] using this } ,
  cont := (DplusCLM (H:=H) (W:=ℂ) f u).continuous }

/-- The Wirtinger gradient `∇₊f[u]`. -/
def gradPlus (f : H → ℂ) (u : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (DplusCLM_c_linear f u)

/-- Defining identity: `D₊f[u][v] = ⟪∇₊f[u], v⟫`. -/
@[simp] lemma inner_gradPlus_eq_Dplus (f : H → ℂ) (u v : H) :
    inner (𝕜 := ℂ) (gradPlus f u) v
      = DplusCLM (H:=H) (W:=ℂ) f u v := by
  change ((InnerProductSpace.toDual ℂ H) (gradPlus f u)) v
          = DplusCLM (H:=H) (W:=ℂ) f u v
  simp [gradPlus, DplusCLM_c_linear]

/-- The map `v ↦ star (DminusCLM f u v)` is a continuous ℂ-linear functional. -/
def DminusCLM_star_c_linear (f : H → ℂ) (u : H) : H →L[ℂ] ℂ :=
{ toLinearMap :=
  { toFun := fun v => star (DminusCLM (H:=H) (W:=ℂ) f u v)
  , map_add' := by intro x y; simp [star_add]
  , map_smul' := by
      intro a v
      set D := DminusCLM (H:=H) (W:=ℂ) f u
      -- from anti-commutation with J: Jc_ℂ ∘ D = - D ∘ Jc_H
      have h0 := congrArg (fun (L : H →L[ℝ] ℂ) => L v)
                  (isALinearR_Dminus (H:=H) (W:=ℂ) f u)
      -- h0 : Jc_ℂ (D v) = - D (Jc_H v)  i.e.  I•D v = - D (I•v)
      have hI : D (I • v) = -I • D v := by
        have : (I : ℂ) • D v = - D ((I : ℂ) • v) := by
          simpa [Jc_apply, ContinuousLinearMap.comp_apply] using h0
        -- negate both sides to put D (I•v) on the left
        have := congrArg Neg.neg this
        -- -(I•D v) = -(- D (I•v)) = D (I•v)
        simpa [neg_smul] using this.symm
      -- decompose `a` and compute
      have ha : a = (a.re : ℂ) + (a.im : ℂ) * I := by
        simpa [mul_comm] using (Complex.re_add_im a).symm
      calc
        star (D (a • v))
            = star (D (((a.re : ℂ) + (a.im : ℂ) * I) • v)) := by simpa [ha]
        _   = star (D ((a.re : ℂ) • v + ((a.im : ℂ) * I) • v)) := by
                simpa [add_smul]
        _   = star (D ((a.re : ℝ) • v + (a.im : ℝ) • (I • v))) := by
                -- definally convert summands to ℝ-smul form
                have hA : ((a.re : ℂ) • v) = (a.re : ℝ) • v := rfl
                have hB : (((a.im : ℂ) * I) • v) = (a.im : ℝ) • (I • v) := by
                  simpa [smul_smul]
                simpa [hA, hB]
        _   = star ((a.re : ℝ) • D v + (a.im : ℝ) • D (I • v)) := by
                simpa [D.map_add, D.map_smul]
        _   = (a.re : ℝ) • star (D v) + (a.im : ℝ) • star (D (I • v)) := by
                -- star is ℝ-linear
                simp [star_add, star_smul]
        _   = (a.re : ℝ) • star (D v) + (a.im : ℝ) • star (-I • D v) := by
                simpa [hI]
        _   = (a.re : ℝ) • star (D v) + (a.im : ℝ) • ((star (-I)) • star (D v)) := by
                simp [star_smul]
        _   = (a.re : ℝ) • star (D v) + (a.im : ℝ) • (I • star (D v)) := by
                -- star(-I) = I since star I = -I
                simp [star_neg, Complex.conj_I]
        _   = a • star (D v) := by
                -- turn ℝ-smul into multiplication and recombine
                have : (a.re : ℝ) • star (D v) + (a.im : ℝ) • (I • star (D v))
                      = ((a.re : ℂ) + (a.im : ℂ) * I) * star (D v) := by
                  simp [Algebra.smul_def, add_mul, mul_add, mul_comm, mul_left_comm, mul_assoc]
                simpa [ha, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] using this } ,
  cont := (continuous_star.comp (DminusCLM (H:=H) (W:=ℂ) f u).continuous) }

/-- The Wirtinger gradient `∇₋f[u]`. -/
def gradMinus (f : H → ℂ) (u : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (DminusCLM_star_c_linear f u)

/-- Defining identity: `D₋f[u][v] = ⟪v, ∇₋f[u]⟫`. -/
@[simp] lemma Dminus_eq_inner_gradMinus (f : H → ℂ) (u v : H) :
    DminusCLM (H:=H) (W:=ℂ) f u v
      = inner (𝕜 := ℂ) v (gradMinus f u) := by
  -- First, `⟪∇₋f[u], v⟫ = star (D₋f[u][v])` by construction.
  have h : inner (𝕜 := ℂ) (gradMinus f u) v
            = star (DminusCLM (H:=H) (W:=ℂ) f u v) := by
    change ((InnerProductSpace.toDual ℂ H) (gradMinus f u)) v
            = star (DminusCLM (H:=H) (W:=ℂ) f u v)
    simp [gradMinus, DminusCLM_star_c_linear]
  -- Now flip slots using conjugate symmetry.
  calc
    DminusCLM (H:=H) (W:=ℂ) f u v
        = star (star (DminusCLM (H:=H) (W:=ℂ) f u v)) := by simp
    _   = star (inner (𝕜 := ℂ) (gradMinus f u) v) := by simpa [h]
    _   = inner (𝕜 := ℂ) v (gradMinus f u) := by
            simpa using (inner_star_eq_swap (gradMinus f u) v)

/-- Split of the real Gâteaux derivative in terms of the Wirtinger gradients. -/
lemma fderivR_apply_split_grad (f : H → ℂ) (u v : H) :
    fderivR (H:=H) (W:=ℂ) f u v
      = inner (𝕜 := ℂ) (gradPlus f u) v
        + inner (𝕜 := ℂ) v (gradMinus f u) := by
  simpa [inner_gradPlus_eq_Dplus, Dminus_eq_inner_gradMinus] using
    (fderivR_apply_split (H:=H) (W:=ℂ) f u v)

end Wirtinger
