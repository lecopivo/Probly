import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.Density
import Mathlib.Control.Random
import Mathlib.Data.Erased

import Probly.Simps


-- import Probly.Erased

open MeasureTheory

open ENNReal BigOperators Finset

namespace Probly


noncomputable
scoped instance : Coe (Erased α) α := ⟨fun x => x.out⟩

abbrev erase (a : α) : Erased α := .mk a

attribute [coe] Erased.out

variable {X Y} [MeasurableSpace X] [MeasurableSpace Y]

@[simp]
theorem lower_integral_direc (f : X → ℝ≥0∞) :
    (∫⁻ x', f x' ∂(Measure.dirac x)) = f x := sorry

@[simp]
theorem integral_direc {Y} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) :
    (∫ x', f x' ∂(Measure.dirac x)) = f x := sorry

@[simp]
theorem dirac_of_set (x : X) (A : Set X) :
    (Measure.dirac x) A = Set.indicator A (fun _ => 1) x := sorry

@[simp]
theorem lower_integral_indicator (c : ℝ≥0∞) (A : Set X) (μ : Measure X) :
    (∫⁻ x, Set.indicator A (fun _ => c) x ∂μ) = c * μ A := sorry

@[simp]
theorem lower_integral_indicator_fun (f : X → ℝ≥0∞) (A : Set X) (μ : Measure X) :
    (∫⁻ x, Set.indicator A f x ∂μ) = (∫⁻ x in A, f x ∂μ) := sorry

@[simp]
theorem lower_integral_indicator_preimage (f : X → Y) (A : Set Y) (μ : Measure X) :
    (∫⁻ x, Set.indicator A (fun _ => 1) (f x) ∂μ) = μ.map f A := sorry


/-- `x : Rand X` is a random variable of type `X`

You can draw a sample by `x.get : IO X`.
Specification of this random variable is given by the probability measure `x.μ`. -/
structure Rand (X : Type) [MeasurableSpace X] where
  /-- Probability measure of the random variable
  We use `Erased` because `μ : Measure X` is usually noncomputable but we want keep
  computable `Rand X` -/
  μ : Erased (Measure X)
  is_prob : IsProbabilityMeasure μ.out
  /-- Object that can generate random samples from `X` according to the prob measure `μ` -/
  rand : _root_.Rand X   -- ugh why doesn't mathlib have `Mathlib` namespace?
  -- TODO: Add some kind of specification that `rand` and `μ` are aligned.
  --       I have no idea how to do that.


noncomputable
instance [MeasurableSpace X] : CoeFun (Erased (Measure X)) (fun _ => Set X → ℝ≥0∞) where
  coe μ A := μ.out A

@[rand_simp,simp]
theorem erase_out {α} (a : α) : (erase a).out = a := sorry

instance (x : Rand X) : IsProbabilityMeasure (x.μ.out) := x.is_prob

@[ext]
theorem Rand.ext (x y : Rand X) : x.μ = y.μ → x.rand = y.rand → x = y := sorry


def Rand.get (x : Rand X) : IO X := do
  let stdGen ← ULiftable.up IO.stdGenRef.get
  let (res, new) := x.rand stdGen
  let _ ← ULiftable.up (IO.stdGenRef.set new.down)
  pure res



noncomputable
def Rand.pdf' (x : Rand X) (ν : Measure X) : X → ℝ≥0∞ :=
  Measure.rnDeriv x.μ ν


noncomputable
abbrev Rand.pdf {X} [MeasureSpace X] (x : Rand X) : X → ℝ≥0∞ := x.pdf' MeasureSpace.volume


-----------------------
-- Monadic structure --
-----------------------

def Rand.pure (x : X) : Rand X where
  μ := erase (Measure.dirac x)
  is_prob := sorry
  rand := Pure.pure x

def Rand.bind (x : Rand X) (f : X → Rand Y) : Rand Y where
  μ := erase {
    measureOf := fun A => ∫⁻ x', (f x').μ A ∂x.μ
    empty := sorry
    mono := sorry
    iUnion_nat := sorry
    m_iUnion := sorry
    trimmed := sorry
  }
  is_prob := sorry
  rand := do (f (← x.rand)).rand

instance [MeasurableSpace α]: Coe α (Rand α) := ⟨Rand.pure⟩

@[simp]
theorem Rand.bind_pure (x : Rand X) :
    (x.bind Rand.pure) = x := by simp[Rand.bind,Rand.pure]; ext <;> simp

@[simp]
theorem Rand.pure_bind (x : X) (f : X → Rand Y) :
    (Rand.pure x |>.bind f) = f x := by simp[Rand.bind,Rand.pure]; ext <;> simp

@[simp]
theorem bind_pdf (ν : Measure Y) (x : Rand X) (f : X → Rand Y) :
    (x.bind f).pdf' ν = fun y => ∫⁻ x', ((f x').pdf' ν y) ∂x.μ := by
  funext y; simp[Rand.pdf',Rand.bind,Rand.pure]; sorry


section Expected
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

noncomputable
def Rand.expectedValue (x : Rand X) (f : X → Y) : Y :=
  ∫ x', f x' ∂(x.μ.out)

noncomputable
def Rand.mean (x : Rand X) : X := x.expectedValue id


@[rand_simp]
theorem expectedValue_pure (x : X) (φ : X → Y) : 
    (Rand.pure x).expectedValue φ = φ x := by simp[Rand.pure,Rand.expectedValue]

@[rand_simp]
theorem expectedValue_bind_pure (x : Rand X) (f : X → Y) (φ : Y → Z) : 
    (x.bind (fun x' => Rand.pure (f x'))).expectedValue φ 
    = 
    x.expectedValue (fun x => φ (f x)) := by 

  simp[Rand.pure,Rand.bind,Rand.expectedValue]
  sorry


theorem expectedValue_to_bind (x : Rand X) (φ : X → Y) :
    x.expectedValue φ = (x.bind (fun x' => Rand.pure (φ x'))).mean := sorry

end Expected


-- I think this is true only almost everywhere. Thus false as stated
theorem bind_μ_apply (x : Rand X) (f : X → Rand Y) (A : Set Y):
    (x.bind f).μ A = ∫⁻ x', (f x').μ A ∂x.μ := by simp[Rand.bind,Rand.pure]

@[simp]
theorem pure_bind_μ (x : X) (f : X → Rand Y) :
    ((Rand.pure x).bind f).μ = (f x).μ := by ext A _; simp[Rand.pure,Rand.bind]

@[simp]
theorem pure_bind_pdf (ν : Measure Y) (x : X) (f : X → Rand Y) :
    ((Rand.pure x).bind f).pdf' ν = (f x).pdf' ν := by simp

@[simp]
theorem bind_pure_μ (x : Rand X) (f : X → Y) :
    (x.bind (fun x' => Rand.pure (f x'))).μ.out = .map f x.μ := by ext A _; simp[Rand.pure,Rand.bind]

----------------------------------------------------------------------------------------------------
-- Notation ----------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

-- we can't use do notation because Rand is not a monad right now (because of the [MeasurableSpace X] argument)
-- this is a small hack to recover it a bit

macro "let" x:Lean.Parser.Term.funBinder " ~ " y:term:max Lean.Parser.semicolonOrLinebreak z:term : term => `(Rand.bind $y (fun $x => $z))

open Lean in
partial def _root_.Lean.Syntax.semicolonToNewline : Syntax → Syntax
| .node info kind args => .node info kind (args.map fun s => semicolonToNewline s)
| .atom info val => if val == ";" then .atom info "\n" else .atom info val
| s => s

@[app_unexpander Rand.bind] def unexpandRandBind : Lean.PrettyPrinter.Unexpander

  | `($(_) $mx:term $f) =>
    match f.raw with
    | `(fun $x:term => $b:term) => do
        let s ← `(let $x ~ $mx; $b)
        pure s.raw -- .semicolonToNewline
    | `($f) => do
        let s ← `(let x ~ $mx; $f x)
        pure s.raw -- .semicolonToNewline
  | _ => throw ()


----------------------------------------------------------------------------------------------------
-- Concrete distributions --------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

/-- Random natural number in the range `lo ≤ n ≤ hi`. -/
def randNat (lo hi : ℕ) : Rand ℕ where
  μ := erase Measure.count
  is_prob := sorry
  rand := fun g => do
    let g : StdGen := g.down
    let (n,g) := _root_.randNat g lo hi
    pure (n, ← ULiftable.up g)

@[simp]
theorem randNat_integral (lo hi : Nat) (f : ℕ → ℝ≥0∞) :
    ∫⁻ n, f n ∂(randNat lo hi).μ = (1/(hi-lo+1) : ℝ≥0∞) * ∑ n in Icc lo hi, f n := sorry

@[simp]
theorem randNat_pdf (lo hi : Nat) (f : ℕ → ℝ≥0∞) :
    (randNat lo hi).pdf' .count = (Icc lo hi).toSet.indicator (fun _ => (1/(hi-lo+1) : ℝ≥0∞)) := sorry



----------------------------------------------------------------------------------------------------
-- More simp theorems ------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


@[simp]
theorem pdf_ite (c : Prop) [h : Decidable c] (t e : Rand X) (ν : Measure X) (x : X) :
  Rand.pdf' (if c then t else e) ν x = if c then t.pdf' ν x else e.pdf' ν x := sorry


@[simp]
theorem pdf_pure (x : X) [DecidableEq X] :
    (Rand.pure x).pdf' Measure.count = fun x' => if x=x' then 1 else 0 := by
  conv => lhs; simp[Rand.pure,Rand.pdf']
  sorry



