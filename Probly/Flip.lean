import Probly.FwdRandDeriv

open MeasureTheory ENNReal BigOperators Finset

namespace Probly

opaque _root_.Float.toReal (x : Float) : ℝ 


def flip (x : ℝ) : Rand Bool := {
  μ := 
    let t := (ENNReal.ofReal x)     -- todo: clamp to [0,1]
    let f := (ENNReal.ofReal (1-x)) -- todo: clamp to [0,1]
    erase (t • Measure.dirac true + f • Measure.dirac false)
  is_prob := sorry
  rand := sorry 
    -- fun g => do
    -- let g : StdGen := g.down
    -- let N := 1000000000000000000000
    -- let (n,g) := _root_.randNat g 0 N
    -- let y := Float.ofNat n / Float.ofNat N
    -- let b := if y ≤ x then true else false
    -- pure (b, ← ULiftable.up g)
}


def dflip : DRand Bool := {
  dμPos := erase (Measure.dirac true)
  dμNeg := erase (Measure.dirac false)
  finite_pos := sorry
  finite_neg := sorry
  dμ_real_zero := by aesop
}


@[rand_simp]
theorem flip.pdf (x : ℝ) (hx : x ∈ Set.Icc 0 1) : 
    (flip x).pdf' .count 
    = 
    fun b => if b then .ofReal x else .ofReal (1-x) := sorry


variable 
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]


@[rand_simp]
theorem flip.arg_x.randDeriv_rule (x : W → ℝ) (hf : Differentiable ℝ x) :
    randDeriv (fun w => flip (x w))
    = 
    fun w dw => 
      let dx' := (fderiv ℝ x w dw) 
      dx' • dflip := sorry


@[rand_simp]
theorem flip.arg_x.randFwdDeriv_rule (x : W → ℝ) (hf : Differentiable ℝ x) :
    randFwdDeriv (fun w => flip (x w))
    = 
    fun w dw => 
      let x'  := (x w)
      let dx' := (fderiv ℝ x w dw)
      ⟨flip x', dx' • dflip⟩ := by
 
  unfold randFwdDeriv; simp (disch:= first | apply hf | sorry) [rand_simp]
  rw[flip.arg_x.randDeriv_rule _ differentiable_id']
  simp


@[rand_simp]
theorem flip.arg_x.randFwdDeriv_rule_siple :
    randFwdDeriv (fun x => flip x)
    = 
    fun x dx => 
      ⟨flip x, dx • dflip⟩ := by
 
  unfold randFwdDeriv; simp (disch:= first | apply hf | sorry) [rand_simp]
  rw[flip.arg_x.randDeriv_rule _ differentiable_id']
  simp
