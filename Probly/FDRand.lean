import Mathlib.MeasureTheory.Measure.VectorMeasure
import Probly.DRand

open MeasureTheory ENNReal BigOperators Finset

namespace Probly

structure FDRand (X : Type) [MeasurableSpace X] where
  val  : Rand X
  dval : DRand X

variable {X Y} [MeasurableSpace X] [MeasurableSpace Y]

def FDRand.pure (x dx : X) : FDRand X := {  
  val  := Rand.pure x
  dval := DRand.pure dx
 }

def FDRand.bind (x : FDRand X) (f : X → FDRand Y) : FDRand Y := {
  val  := x.val.bind (fun x' => (f x').val)
  dval := x.dval.bind (fun x' => (f x').val) + 
          x.val.dbind (fun x' => (f x').dval)
}

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

#check IsFiniteMeasure

noncomputable
def FDRand.expectedValue (x : FDRand X) (f : X → Y) : Y :=
  ∫ x', f x' ∂(x.val.μ.out)
  +
  ∫ x', f x' ∂(x.dval.dμPos.out)
  -
  ∫ x', f x' ∂(x.dval.dμNeg.out)

noncomputable 
def FDRand.mean (x : FDRand X) : X := x.expectedValue id

macro "let" x:Lean.Parser.Term.funBinder " ~~ " y:term:max Lean.Parser.semicolonOrLinebreak z:term : term => `(bind₂ $y (fun $x => $z))


@[app_unexpander FDRand.bind] def unexpandFDRandBind : Lean.PrettyPrinter.Unexpander

  | `($(_) $mx:term $f) => 
    match f.raw with
    | `(fun $x:term => $b:term) => do
        let s ← `(let $x ~~ $mx; $b)
        pure s.raw -- .semicolonToNewline
    | `($f) => do
        let s ← `(let x ~~ $mx; $f x)
        pure s.raw -- .semicolonToNewline
  | _ => throw ()
