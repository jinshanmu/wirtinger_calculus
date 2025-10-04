/-
Adjoint of a continuous conjugate-linear map B : E → F.

Conventions (mathlib): `inner` is conjugate-linear in the 1st slot, linear in the 2nd.
We build (conjAdjoint B) : F → E and prove:
  inner ((conjAdjoint B) x) y = inner (B y) x
  inner x (B y) = star (inner ((conjAdjoint B) x) y)
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Complex.Basic

noncomputable section

namespace ConjAdj

/-- For fixed `x : F`, the bounded linear functional `y ↦ inner (B y) x`. -/
private def phi
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (B : E → F)
  (h_add  : ∀ y z, B (y + z) = B y + B z)
  (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
  (h_cont : Continuous B)
  (x : F) : E →L[ℂ] ℂ :=
by
  classical
  -- 1) Underlying linear map (linear in y since B is conjugate-linear):
  let L : E →ₗ[ℂ] ℂ :=
  { toFun := fun y => inner (𝕜 := ℂ) (B y) x
  , map_add' := by
      intro y z
      simp [h_add y z, inner_add_left]
  , map_smul' := by
      intro a y
      -- B (a•y) = star a • B y; first slot conjugate-linear:
      -- inner ((star a) • B y) x = a * inner (B y) x
      simp [h_smul a y, inner_smul_left, star_star, mul_comm] }
  -- 2) Continuity: y ↦ inner (B y) x = star (inner x (B y))
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
    ext y; simp [L, inner_conj_symm]
  -- 3) Package:
  exact { toLinearMap := L, cont := hLcont }

/-- Adjoint of a conjugate-linear `B`, via the Riesz isometry. -/
def conjAdjoint
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (B : E → F)
  (h_add  : ∀ y z, B (y + z) = B y + B z)
  (h_smul : ∀ (a : ℂ) y, B (a • y) = (star a) • B y)
  (h_cont : Continuous B) :
  F → E :=
fun x => (InnerProductSpace.toDual ℂ E).symm (phi B h_add h_smul h_cont x)

/-- Riesz characterization for the conjugate-linear adjoint:
`inner ((conjAdjoint B) x) y = inner (B y) x`. -/
lemma inner_conjAdjoint
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (B : E → F)
  (h_add  : ∀ y z, B (y + z) = B y + B z)
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
  simp [conjAdjoint, phi, h_add, h_smul]

/-- Formal adjoint identity (your requested form):
`inner x (B y) = star (inner ((conjAdjoint B) x) y)`. -/
lemma inner_eq_star_adjoint
  {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (B : E → F)
  (h_add  : ∀ y z, B (y + z) = B y + B z)
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

end
