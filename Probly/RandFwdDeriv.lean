import Probly.RandDeriv
import Probly.FDRand


open MeasureTheory ENNReal BigOperators Finset

namespace Probly

open Rand

variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]



----------------------------------------------------------------------------------------------------
-- Lambda and Monadic Rules ------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[rand_simp,simp]
theorem randFwdDeriv_const (a : Rand α) :
    randFwdDeriv (fun _ : W => a)
    =
    fun _ _ => ⟨a,0⟩ := by

  unfold randFwdDeriv
  simp only [rand_simp]


@[rand_simp,simp]
theorem randFwdDeriv_comp (f : Y → Rand Z) (g : X → Y)
    (hf : RandDifferentiable f) (hg : Differentiable ℝ g) :
    randFwdDeriv (fun x : X => (f (g x)))
    =
    fun x dx =>
      let y := g x -- todo: use normal forward derivative
      let dy := fderiv ℝ g x dx
      randFwdDeriv f y dy := by

  funext x dx
  unfold randFwdDeriv
  simp (disch := first | apply hf | apply hg) only [rand_simp,randDeriv_comp]


@[rand_simp,simp]
theorem FDRand.pure.arg_x.randFwdDeriv_rule (x : W → X) (hx : Differentiable ℝ x) :
    randFwdDeriv (fun w => pure (x w))
    =
    fun w dw =>
      fdpure (x w) (fderiv ℝ x w dw) := by

  unfold randFwdDeriv fdpure
  simp (disch:=first | apply hx | sorry) only [rand_simp]
  funext w dw
  rw [Rand.pure.arg_x.randDeriv_rule _ differentiable_id']
  simp


@[rand_simp,simp]
theorem FDRand.pure.arg_x.randFwdDeriv_rule_simple :
    randFwdDeriv (fun x : X => Rand.pure x)
    =
    fun x dx =>
      fdpure x dx := by

  unfold randFwdDeriv fdpure
  simp (disch:=first | apply hx | sorry) [rand_simp]
  funext w dw
  rw [Rand.pure.arg_x.randDeriv_rule _ differentiable_id']
  simp (disch:=first | apply hx | sorry) [rand_simp]


@[rand_simp,simp]
theorem Rand.bind.arg_xf.randFwdDeriv_rule (x : W → Rand α) (f : W → α → Rand β)
    (hx : RandDifferentiable x) (hf : ∀ x, RandDifferentiable (f · x)) :
    randFwdDeriv (fun w => (x w).bind (f w ·))
    =
    fun w dw => (randFwdDeriv x w dw).bind (fun x => randFwdDeriv (f · x) w dw) := by

  unfold randFwdDeriv FDRand.bind
  simp (disch:=first | apply hx | apply hf) only [rand_simp]



----------------------------------------------------------------------------------------------------
-- Other Rules -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

@[rand_simp,simp]
theorem ite.arg_tf.randFwdDeriv_rule {c} [Decidable c] (t f : W → Rand α) :
    randFwdDeriv (fun w => if c then (t w) else (f w))
    =
    fun w dw => if c then randFwdDeriv t w dw else randFwdDeriv f w dw := by
  if h : c then simp[h] else simp[h]
