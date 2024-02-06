import Probly.Init
import Probly.Simps

import Mathlib.MeasureTheory.Measure.GiryMonad


open MeasureTheory ENNReal BigOperators Finset


namespace Probly




/-- `x : Rand X` is a random variable of type `X`

You can draw a sample by `x.get : IO X`.
Specification of this random variable is given by the probability measure `x.μ`.

This is Giry monad + its computational realization that can draw random samples.

TODO: Add some kind of specification that `rand` corresponds to `μ`.
      See doc of `Rand.ext` for more discussion. -/
structure Rand (X : Type) [MeasurableSpace X] where
  /-- Probability measure of the random variable
  We use `Erased` because `μ : Measure X` is usually noncomputable but we want keep
  computable `Rand X` -/
  μ : Erased (Measure X)
  is_prob : IsProbabilityMeasure μ.out
  /-- Object that can generate random samples from `X` according to the prob measure `μ` -/
  rand : _root_.Rand X   -- ugh why doesn't mathlib have `Mathlib` namespace?

variable
  {X} [MeasurableSpace X]
  {Y} [MeasurableSpace Y]
  {Z} [MeasurableSpace Z]

instance (x : Rand X) : IsProbabilityMeasure (x.μ.out) := x.is_prob

namespace Rand

/-- Extensionality of random variable.

WARNING: This theorem is inconsistent!!! The random generators `x.rand` and `y.rand` might differ.
         We are not trying to model pseudo-random numbers. We assume that every random number
         generator is a true random number generator. Thus the result of any probabilistic program
         should be independent on the exact generator up to some randomness.

TODO: We might quotient all the random number generators corresponding to the measure `x.μ`  under
      the assumption that they are all true random generators. I believe that such type would be
      a singleton i.e. all the random number generators are all the same.
-/
@[ext]
axiom ext (x y : Rand X) : x.μ = y.μ → x = y


/-- Generate rundom number using IO randomness -/
def get (x : Rand X) : IO X := do
  let stdGen ← ULiftable.up IO.stdGenRef.get
  let (res, new) := x.rand stdGen
  let _ ← ULiftable.up (IO.stdGenRef.set new.down)
  pure res


-- in mathlib this is: MeasurableSpace X → MeasurableSpace (Measure X)
instance : MeasurableSpace (Rand X) := sorry

theorem is_measurable {f : X → Rand Y} (hf : Measurable f) :
    Measurable (fun x => (f x).μ.out) := sorry


----------------------------------------------------------------------------------------------------
-- Probability of an event  ------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

noncomputable
def probability (x : Rand X) (s : Set X) : ℝ≥0∞ := x.μ s


----------------------------------------------------------------------------------------------------
-- Monadic structure -------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

def pure (x : X) : Rand X where
  μ := erase (Measure.dirac x)
  is_prob := sorry
  rand := Pure.pure x

def bind (x : Rand X) (f : X → Rand Y) : Rand Y where
  μ := erase (x.μ.out.bind (fun x => (f x).μ))
  is_prob := sorry
  rand := do (f (← x.rand)).rand

def join (x : Rand (Rand X)) : Rand X := x.bind id

-- instance [MeasurableSpace α]: Coe α (Rand α) := ⟨pure⟩


@[rand_simp,simp]
theorem bind_probability (x : Rand X) (f : X → Rand Y) (s : Set Y) (hs : MeasurableSet s)
    (hf : Measurable f) : (bind x f).probability s = ∫⁻ x', (f x').probability s ∂x.μ.out := by

  have := is_measurable hf
  simp (disch:=assumption) [bind, probability, Measure.bind_apply]


theorem measurable_pure' {f : X → Y} (hf : Measurable f) : Measurable fun x => pure (f x) :=
  sorry

theorem measurable_bind' {f : X → Rand Y} (hf : Measurable f) : Measurable fun x => bind x f :=
  sorry


@[rand_simp,simp]
theorem lintegral_bind (x : Rand X) (f : X → Rand Y) (φ : Y → ℝ≥0∞) (hf : Measurable f)
    (hφ : Measurable φ) : ∫⁻ x', φ x' ∂(bind x f).μ = ∫⁻ x', ∫⁻ y', φ y' ∂(f x').μ ∂x.μ := by

  simp [bind]
  apply Measure.lintegral_bind (is_measurable hf) hφ


@[rand_simp,simp]
theorem bind_bind (x : Rand X) (g : X → Rand Y) (f : Y → Rand Z)
    (hg : Measurable g) (hf : Measurable f) : bind (bind x g) f = bind x fun x' => bind (g x') f := by

  ext; simp [bind]
  rw[Measure.bind_bind (m:=x.μ) (is_measurable hg) (is_measurable hf)]


@[rand_simp,simp]
theorem bind_pure (f : X → Rand Y) (hf : Measurable f) (x : X) : bind (pure x) f = f x := by
  ext; simp[bind,pure]
  rw[Measure.bind_dirac (is_measurable hf) x]


----------------------------------------------------------------------------------------------------
-- Notation ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- we can't use do notation because Rand is not a monad right now (because of the [MeasurableSpace X] argument)
-- this is a small hack to recover it a bit
open Lean.Parser Term in
syntax withPosition("let" funBinder " ~ " term semicolonOrLinebreak ppDedent(ppLine) term) : term
macro_rules
  | `(let $x ~ $y; $b) => do Pure.pure (← `(Probly.Rand.bind $y (fun $x => $b))).raw

open Lean Parser
@[app_unexpander Rand.bind] def unexpandRandBind : Lean.PrettyPrinter.Unexpander

| `($(_) $y $f) =>
  match f.raw with
  | `(fun $x:term => $b) => do
    let s ←
      `(let $x ~ $y
        $b)
    Pure.pure s.raw
  | _ => throw ()

| _ => throw ()


----------------------------------------------------------------------------------------------------
-- Arithmetics -------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

instance [Add X] : HAdd X (Rand X) (Rand X) := ⟨fun x' x =>
  let x'' ~ x
  pure (x' + x'')⟩

instance [Add X] : HAdd (Rand X) X (Rand X) := ⟨fun x x' =>
  let x'' ~ x
  pure (x'' + x')⟩

-- instance [Add X] : HAdd (Rand X) (Rand X) (Rand X) := ⟨fun x y =>
--   let x' ~ x
--   let y' ~ y
--   pure (x' + y')⟩

-- todo: add simp theorems that inline these operations


----------------------------------------------------------------------------------------------------
-- Expected Value ----------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

section ExpectedValue

variable
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]


@[rand_simp,simp]
theorem integral_pure (x : X) (φ : X → Y) (hφ : Measurable φ) :
    ∫ x', φ x' ∂(pure x).μ = φ x := sorry


-- todo: I think we need some integrability here
@[rand_simp,simp]
theorem integral_bind (x : Rand X) (f : X → Rand Y) (φ : Y → Z) (hf : Measurable f)
    (hφ : Measurable φ) : ∫ x', φ x' ∂(bind x f).μ = ∫ x', ∫ y', φ y' ∂(f x').μ ∂x.μ := sorry


noncomputable
def expectedValue (x : Rand X) (φ : X → Y) : Y :=
  ∫ x', φ x' ∂x.μ

noncomputable
abbrev E (x : Rand X) (φ : X → Y) : Y := x.expectedValue φ

@[rand_simp,simp]
theorem pure_E (x : X) (φ : X → Y) :
    (pure x).E φ = φ x := by
  simp (disch:=sorry) only [E,expectedValue,rand_simp]

@[rand_simp,simp]
theorem bind_E (x : Rand X) (f : X → Rand Y) (φ : Y → Z) :
    (x.bind f).E φ = x.E (fun x' => (f x').E φ) := by
  simp (disch:=sorry) only [E,expectedValue,rand_simp]

@[rand_simp,simp]
theorem zero_E (x : Rand X)  :
    x.E (fun _ => (0 :Y )) = 0 := by
  simp only [E,expectedValue,integral_zero]


@[rand_simp,simp]
theorem expectedValue_smul (x : Rand X) (φ : X → ℝ) (y : Y) :
    x.E (fun x' => φ x' • y) = x.E φ • y := by sorry

noncomputable
def mean (x : Rand X) : X := x.E id

theorem expectedValue_as_mean (x : Rand X) (φ : X → Y) (hφ : Measurable φ) :
    x.E φ = (x.bind (fun x' => pure (φ x'))).mean := by

  simp (disch:=sorry) [mean,expectedValue,E,hφ]

theorem mean_add  (x : Rand X) (x' : X) : x.mean + x' = (HAdd.hAdd x  x').mean := sorry
theorem mean_add' (x : Rand X) (x' : X) : x' + x.mean = (HAdd.hAdd x' x).mean  := sorry

end ExpectedValue


----------------------------------------------------------------------------------------------------
-- Probability density function --------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Probability density function of `x` w.r.t. the measure `ν`. -/
noncomputable
def pdf' (x : Rand X) (ν : Measure X) : X → ℝ≥0∞ :=
  Measure.rnDeriv x.μ ν

/-- Probability density function of `x` w.r.t. the intrinsic volume measure. -/
noncomputable
abbrev pdf {X} [MeasureSpace X] (x : Rand X) : X → ℝ≥0∞ := x.pdf' MeasureSpace.volume


/-- To actually compute values of pdf use this version of pdf where you can specify the scalar type.
Transformation rules should trun it into a computable function. -/
noncomputable
abbrev cpdf' {X} [MeasureSpace X] (R : Type) [IsROrC R] (x : Rand X) (ν : Measure X) : X → R :=
  sorry -- turn `(x.pdf' ν).toReal` to `R` but `IsROrC` does not have such a function :(


@[rand_simp,simp]
theorem bind_pdf (ν : Measure Y) (x : Rand X) (f : X → Rand Y) :
    (x.bind f).pdf' ν = fun y => ∫⁻ x', ((f x').pdf' ν y) ∂x.μ := by
  funext y; simp[Rand.pdf',Rand.bind,Rand.pure]; sorry
