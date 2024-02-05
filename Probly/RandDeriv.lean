import Mathlib.Analysis.Calculus.FDeriv.Basic

import Probly.DRand
import Probly.RewriteBy

namespace Probly

open MeasureTheory ENNReal BigOperators Finset


/-- `f` is differentiable as a function from space `X` to the space of finite measures with finite total variation. -/
opaque RandDifferentiable {X} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y} [MeasurableSpace Y]
    (f : X → Rand Y) : Prop 


def randDeriv {X} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y} [MeasurableSpace Y]
    (f : X → Rand Y) (x dx : X) : DRand Y := {
  -- differentiate `f` as a functin from `X` to the space of finite measures
  -- with finite total variation and then split it to positive and negative part
  dμPos := sorry
  dμNeg := sorry
  finite_pos := sorry
  finite_neg := sorry
  dμ_real_zero := sorry
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


@[rand_simp]
theorem randDeriv_const (a : Rand α) : 
    randDeriv (fun w : W => a)
    =
    fun w dw => 0 := sorry


@[rand_simp]
theorem randDeriv_comp (f : Y → Rand Z) (g : X → Y) 
    (hf : RandDifferentiable f) (hg : Differentiable ℝ g) : 
    randDeriv (fun x : X => (f (g x)))
    =
    fun x dx => 
      let y := g x
      let dy := fderiv ℝ g x dx
      randDeriv f y dy := sorry



-- !!!!THIS IS INCORRECT!!!!
@[rand_simp]
theorem Rand.pure.arg_x.randDeriv_rule (x : W → X) (hx : Differentiable ℝ x) : 
    randDeriv (fun w => Rand.pure (x w))
    =
    fun w dw => DRand.pure (fderiv ℝ x w dw) := sorry


@[rand_simp]
theorem Rand.bind.arg_xf.randDeriv_rule (x : W → Rand α) (f : W → α → Rand β) 
    (hx : RandDifferentiable x) (hf : ∀ x, RandDifferentiable (f · x)) : 
    randDeriv (fun w => (x w).bind (f w ·)) 
    =
    fun w dw => (randDeriv x w dw).bind (f w · )
                +
                (x w).dbind (fun x => randDeriv (f · x) w dw) := sorry





@[rand_simp]
theorem ite.arg_tf.randDeriv_rule {c} [Decidable c]
    (t f : W → Rand α) (ht : RandDifferentiable t) (hf : RandDifferentiable f) :
    randDeriv (fun w => if c then (t w) else (f w)) 
    =
    fun w dw => if c then randDeriv t w dw else randDeriv f w dw := sorry
