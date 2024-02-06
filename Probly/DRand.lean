import Mathlib.MeasureTheory.Measure.VectorMeasure
import Mathlib.Analysis.Calculus.FDeriv.Basic

import Probly.Basic


open MeasureTheory ENNReal BigOperators Finset

namespace Probly

structure DRand (X : Type) [MeasurableSpace X] where
  -- this should do the correct action on test functions and give up on non-smooth ones
  -- there should be some integrability requirement on the test function too
  -- question is can we enlarge the domain to:
  --   1. differentiable function with or without compact support?
  action : (X → ℝ) → ℝ
  -- todo: require that action returns zero on non-test functions

variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]

-- todo: some smoothenss
theorem DRand.ext (x y : DRand X) : (∀ φ, x.action φ = y.action φ)→ x = y := sorry

instance : Zero (DRand X) := ⟨{
  action := fun φ => 0
}⟩

instance : Add (DRand X) := ⟨fun x y => {
  action := fun φ => x.action φ + y.action φ
}⟩

noncomputable
instance : SMul ℝ (DRand X) := ⟨fun s x => {
  action := fun φ => s • (x.action φ)
}⟩

-- Extend `F` functional on test function to to a Y-valued functional.
-- not every `f` can have such extension
-- extension is valid if does not depend on the appxosimation of `f` by test functions
noncomputable
opaque testFunctionExtension
  {X} -- X needs a predicat that it has a notion of test functions
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (F : (X → ℝ) → ℝ) (f : X → Y) : Y := sorry

noncomputable
def DRand.expectedValueChange (x : DRand X) (f : X → Y) : Y :=
  testFunctionExtension x.action f

@[rand_simp]
theorem action_zero : (0 : DRand X).action φ = 0 := rfl

-- todo: add some smoothenss assumption on `φ`
@[rand_simp]
theorem action_add (x y : DRand X) (φ : X → ℝ) : (x + y).action φ = x.action φ + y.action φ := rfl

@[rand_simp]
theorem action_smul (s : ℝ) (x : DRand X) (φ : X → ℝ) : (s • x).action φ = s • x.action φ := rfl


noncomputable
def DRand.dpure (x dx : X) : DRand X := {
  action := fun f => fderiv ℝ f x dx
 }

noncomputable
def DRand.bind (x : DRand X) (f : X → Rand Y) : DRand Y := {
  action := fun φ => x.action (fun x' => (∫ y', φ y' ∂(f x').μ))
}

noncomputable
def Rand.dbind (x : Rand X) (f : X → DRand Y) : DRand Y := {
  action := fun φ => ∫ x', (f x').action φ ∂x.μ
}

@[rand_simp]
theorem smul_one_drand (x : DRand X) : (1:ℝ) • x = x := sorry


@[rand_simp]
theorem expecteValueChange_action (x : DRand X) (φ : X → ℝ) :
    x.expectedValueChange φ = x.action φ := sorry


@[rand_simp]
theorem add_expectedValueChange (x y : DRand X) (φ : X → Y) :
    (x + y).expectedValueChange φ 
    = 
    x.expectedValueChange φ + y.expectedValueChange φ := sorry


-- opaque DRand.ρ (x : DRand X) (r : Rand X) : X → ℝ

-- theorem DRand.bind_density (x : DRand X) (r : Rand X) (f : X → Rand Y) (φ : Y → ℝ) :
--     (x.bind f).action φ = (r.bind f).expectedValue (fun x' => (x.ρ r) x' * φ x') := sorry

-- theorem DRand.bind_as_rand_bind (x : DRand X) (f : X → Rand Y) (φ : Y → ℝ) :
--     (x.bind f).action φ = sorry := sorry

-- theorem drand_bind_pure (x : DRand X) (f : X → Y) :
--     x.bind (fun x' => Rand.pure (f x')) = sorry := by
  
--   simp[DRand.bind,Rand.pure,rand_simp]

@[rand_simp]
theorem pure_action (x dx : X) : (DRand.dpure x dx).action φ = fderiv ℝ φ x dx := sorry


@[rand_simp]
theorem bind_action_eq_expectedValue (x : DRand X) (f : X → Rand Y) (φ : Y → ℝ) :
    (x.bind f).action φ = x.action (fun x' => (f x').expectedValue φ) := by

  simp only [DRand.bind,Rand.expectedValue, rand_simp]


@[rand_simp]
theorem dbind_action_eq_expectedValue (x : Rand X) (f : X → DRand Y) (φ : Y → ℝ) :
    (x.dbind f).action φ = x.expectedValue (fun x' => (f x').action φ) := by

  simp only [Rand.dbind,Rand.expectedValue, rand_simp]


