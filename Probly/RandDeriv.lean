import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic

import Probly.DRand
import Probly.RewriteBy

namespace Probly

open MeasureTheory ENNReal BigOperators Finset


/-- I think this should effectively say that the theorem `deriv_measure_under_integral` holds.

That should be easy to verify for dirac measure.
For other random variables we will like battle with integrability conditions. -/
opaque RandDifferentiable {X} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y} [MeasurableSpace Y]
    (f : X → Rand Y) : Prop


noncomputable
def randDeriv {X} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y} [MeasurableSpace Y]
    (f : X → Rand Y) (x dx : X) : DRand Y := {
  -- differentiate `f` as a functin from `X` to the space of finite measures
  -- with finite total variation and then split it to positive and negative part
  action := fun φ => deriv (fun t : ℝ => ∫ y, φ y ∂(f (x+t•dx)).μ) 0
}


section RandDeriv


 -- Probalby I should make sure that we are getting borel spaces
variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]


-- todo: add condition that `φ` is a test function
--       the definition of test function should admit `Z` to be discrete space or vector space
@[rand_simp]
theorem deriv_measure_under_integral {Z} [MeasurableSpace Z] (f : Y → Rand Z) (g : X → Y) (φ : Z → ℝ)
    (hf : RandDifferentiable f) (hg : Differentiable ℝ g) :
    deriv (fun t : ℝ ↦ ∫ (y : Z), φ y ∂↑(f (g (x + t • dx))).μ) 0
    =
    deriv (fun t : ℝ ↦ ∫ (y : Z), φ y ∂↑(f (g x + t • (fderiv ℝ g x) dx)).μ) 0 := sorry


@[rand_simp]
theorem randDeriv_const (a : Rand α) :
    randDeriv (fun _ : W => a)
    =
    fun w dw => 0 := by

  funext w dw
  apply DRand.ext
  intro φ
  simp [randDeriv, rand_simp]


@[rand_simp]
theorem randDeriv_comp {Z} [MeasurableSpace Z] (f : Y → Rand Z) (g : X → Y)
    (hf : RandDifferentiable f) (hg : Differentiable ℝ g) :
    randDeriv (fun x : X => (f (g x)))
    =
    fun x dx =>
      let y := g x
      let dy := fderiv ℝ g x dx
      randDeriv f y dy := by

  funext x dx
  apply DRand.ext; intro φ
  simp [randDeriv, rand_simp]
  simp (disch:=first | assumption | sorry) only [rand_simp]

#check fderiv

@[rand_simp]
theorem Rand.pure.arg_x.randDeriv_rule (x : W → X) (hx : Differentiable ℝ x) :
    randDeriv (fun w => Rand.pure (x w))
    =
    fun w dw => DRand.dpure (x w) (fderiv ℝ x w dw) := by

  funext w dw
  apply DRand.ext; intro φ
  simp [randDeriv, rand_simp, DRand.dpure, Rand.pure]
  sorry


@[rand_simp]
theorem Rand.bind.arg_xf.randDeriv_rule (x : W → Rand α) (f : W → α → Rand β)
    (hx : RandDifferentiable x) (hf : ∀ x, RandDifferentiable (f · x)) :
    randDeriv (fun w => (x w).bind (f w ·))
    =
    fun w dw => (randDeriv x w dw).bind (f w · )
                +
                (x w).dbind (fun x => randDeriv (f · x) w dw) := by

  funext w dw
  apply DRand.ext; intro φ
  simp [randDeriv, rand_simp, DRand.bind, Rand.pure, dbind]
  sorry




@[rand_simp]
theorem ite.arg_tf.randDeriv_rule {c} [Decidable c] (t f : W → Rand α) :
    randDeriv (fun w => if c then (t w) else (f w))
    =
    fun w dw => if c then randDeriv t w dw else randDeriv f w dw := by

  funext w dw
  if h : c then simp [h] else simp [h]
