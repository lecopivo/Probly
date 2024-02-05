import Probly.RandDeriv
import Probly.FDRand


open MeasureTheory ENNReal BigOperators Finset

namespace Probly

def randFwdDeriv {X} [NormedAddCommGroup X] [NormedSpace ℝ X] {Y} [MeasurableSpace Y]
    (f : X → Rand Y) (x dx : X) : FDRand Y := ⟨f x, randDeriv f x dx⟩


variable 
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]


@[rand_simp]
theorem randFwdDeriv_const (a : Rand α) : 
    randFwdDeriv (fun _ : W => a)
    =
    fun _ _ => ⟨a,0⟩ := by

  unfold randFwdDeriv
  simp only [rand_simp]


@[rand_simp]
theorem randFwdDeriv_comp (f : Y → Rand Z) (g : X → Y) 
    (hf : RandDifferentiable f) (hg : Differentiable ℝ g) : 
    randFwdDeriv (fun x : X => (f (g x)))
    =
    fun x dx => 
      let y := g x -- todo: use normal forward derivative
      let dy := fderiv ℝ g x dx 
      randFwdDeriv f y dy := by

  unfold randFwdDeriv
  simp (disch := first | apply hf | apply hg) only [rand_simp] 


@[rand_simp]
theorem FDRand.pure.arg_x.randFwdDeriv_rule (x : W → X) (hx : Differentiable ℝ x) : 
    randFwdDeriv (fun w => Rand.pure (x w))
    =
    fun w dw => 
      FDRand.pure (x w) (fderiv ℝ x w dw) := by

  unfold randFwdDeriv FDRand.pure
  simp (disch:=first | apply hx | sorry) only [rand_simp]
  funext w dw 
  rw [Rand.pure.arg_x.randDeriv_rule _ differentiable_id']
  simp


@[rand_simp]
theorem FDRand.pure.arg_x.randFwdDeriv_rule_simple : 
    randFwdDeriv (fun x : X => Rand.pure x)
    =
    fun x dx => 
      FDRand.pure x dx := by

  unfold randFwdDeriv FDRand.pure
  simp (disch:=first | apply hx | sorry) [rand_simp]
  funext w dw 
  rw [Rand.pure.arg_x.randDeriv_rule _ differentiable_id']
  simp (disch:=first | apply hx | sorry) [rand_simp]


@[rand_simp]
theorem Rand.bind.arg_xf.randFwdDeriv_rule (x : W → Rand α) (f : W → α → Rand β) 
    (hx : RandDifferentiable x) (hf : ∀ x, RandDifferentiable (f · x)) : 
    randFwdDeriv (fun w => (x w).bind (f w ·)) 
    =
    fun w dw => (randFwdDeriv x w dw).bind (fun x => randFwdDeriv (f · x) w dw) := by

  unfold randFwdDeriv FDRand.bind
  simp (disch:=first | apply hx | apply hf) only [rand_simp]



@[rand_simp]
theorem ite.arg_tf.randFwdDeriv_rule {c} [Decidable c]
    (t f : W → Rand α) (ht : RandDifferentiable t) (hf : RandDifferentiable f) :
    randFwdDeriv (fun w => if c then (t w) else (f w)) 
    =
    fun w dw => if c then randFwdDeriv t w dw else randFwdDeriv f w dw := sorry
