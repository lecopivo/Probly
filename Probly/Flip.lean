import Probly.RandFwdDeriv

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
  action := fun φ => φ true - φ false
}


@[rand_simp,simp]
theorem flip.pdf_wrt_flip (θ θ' : ℝ) :
    (flip θ).pdf' (flip θ').μ
    =
    fun b => if b then θ / θ' else (1-θ) / (1-θ') := by sorry

@[rand_simp,simp]
theorem dflip.density_wrt_flip (θ : ℝ) :
    dflip.density (flip θ).μ
    =
    fun b => if b then 1 / θ else 1 / (θ-1) := by sorry


@[rand_simp,simp]
theorem flip.pdf (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    (flip x).pdf' .count
    =
    fun b => if b then x else (1-x) := by sorry


variable
  {W} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
  {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Y]
  {Z} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z]
  {α} [MeasurableSpace α]
  {β} [MeasurableSpace β]

@[rand_simp,simp]
theorem flip_integral (θ : ℝ) (f : Bool → X) :
    ∫ x, f x ∂(flip θ).μ = θ • f true + (1-θ) • f false := by

  simp [flip,rand_simp]

theorem flip_expectedValue (θ : ℝ) (f : Bool → X) :
    (flip θ).E f = θ • f true + (1-θ) • f false := by

  simp[Rand.E,Rand.expectedValue,rand_simp]

theorem dflip_expectedValueChange (f : Bool → X) :
    dflip.dE f = f true - f false := by

  simp [DRand.dE,dflip]
  apply testFunctionExtension_ext
  intro φ y; simp [sub_smul]


@[rand_simp,simp]
theorem flip.arg_x.randDeriv_rule (x : W → ℝ) (hf : Differentiable ℝ x) :
    randDeriv (fun w => flip (x w))
    =
    fun w dw =>
      let dx' := (fderiv ℝ x w dw)
      dx' • dflip := by

  simp (disch:=sorry) [rand_simp]
  funext w dw
  simp [randDeriv]
  apply DRand.ext; intro φ; simp[dflip,rand_simp]
  sorry -- just differentiation and ring


@[rand_simp,simp]
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


@[rand_simp,simp]
theorem flip.arg_x.randFwdDeriv_rule_siple :
    randFwdDeriv (fun x => flip x)
    =
    fun x dx =>
      ⟨flip x, dx • dflip⟩ := by

  unfold randFwdDeriv; simp (disch:= first | apply hf | sorry) [rand_simp]
  rw[flip.arg_x.randDeriv_rule _ differentiable_id']
  simp
