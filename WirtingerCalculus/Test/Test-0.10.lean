import Mathlib

/-!
# Basic.lean — Setup & Notation (single-namespace)

This file provides:

* Complex structure `J` as an `ℝ`-linear map (multiplication by `i`)
* Shorthands `J_H`, `J_W`
* Sandwich `𝒜 T = J_W ∘ T ∘ J_H`
* Wirtinger split on `ℝ`-linear maps: `Tplus`, `Tminus`, and the split lemma
* Predicates `IsCLinearR` / `IsALinearR`
* Hermitian adjoint notation `†` for **complex** continuous linear maps
* Abstract `Conjugation` (ℝ-linear involution anti-commuting with `J`)
* “Adjoint” construction for **conjugate-linear** (anti-linear) maps via `conjAdjoint`

**Convention (mathlib):** the inner product is conjugate-linear in the **first** slot
and linear in the **second** slot. With this convention, for `A : H →L[ℂ] W` one has
`⟪x, A y⟫ = ⟪A† x, y⟫` (equivalently, `⟪A x, y⟫ = ⟪x, A† y⟫`).
For **anti-linear** maps we do *not* overload `†`; instead we provide `conjAdjoint`
with the Riesz identity below.
-/

noncomputable section
open Complex

namespace Wirtinger

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
  calc
    (Tplus T + Tminus T) v
        = (1/2 : ℝ) • (T v - (𝒜 T) v) + (1/2 : ℝ) • (T v + (𝒜 T) v) := by
          simp [Tplus, Tminus, 𝒜, sub_eq_add_neg]
    _ = ((1/2 : ℝ) • T v + (1/2 : ℝ) • T v)
        + ((1/2 : ℝ) • (-(𝒜 T) v) + (1/2 : ℝ) • ((𝒜 T) v)) := by
          simp [smul_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg, smul_neg]
    _ = ((1/2 : ℝ) + (1/2 : ℝ)) • T v + 0 := by
          simp [add_smul, smul_neg]
    _ = (1 : ℝ) • T v := by
          norm_num
    _ = T v := by
          simp

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
variable [AddCommGroup V] [Module ℂ V]
variable [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]

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
variable [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Conjugate symmetry in `star` form. -/
@[simp] lemma inner_star_eq_swap (x y : H) :
    star (inner (𝕜 := ℂ) x y) = inner (𝕜 := ℂ) y x := by
  classical
  change (starRingEnd ℂ) (inner (𝕜 := ℂ) x y) = inner (𝕜 := ℂ) y x
  exact inner_conj_symm (𝕜 := ℂ) y x

end

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
