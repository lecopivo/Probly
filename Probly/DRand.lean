import Mathlib.MeasureTheory.Measure.VectorMeasure

import Probly.Basic


open MeasureTheory ENNReal BigOperators Finset

namespace Probly

structure DRand (X : Type) [MeasurableSpace X] where
  dμPos : Erased (Measure X)
  dμNeg : Erased (Measure X)
  dμ_real_zero : dμPos.out ⊤ = dμNeg.out ⊤
  -- drand : R → _root_.Rand X -- R should have [RealScalar R]


variable {X Y} [MeasurableSpace X] [MeasurableSpace Y]

instance : Add (DRand X) := sorry

def DRand.pure (x : X) : DRand X := {  
  dμPos := erase {
    measureOf := fun A => 0
    empty := rfl
    m_iUnion := sorry
    mono := sorry
    iUnion_nat := sorry
    trimmed := sorry
  }
  dμNeg := erase {
    measureOf := fun A => 0
    empty := rfl
    m_iUnion := sorry
    mono := sorry
    iUnion_nat := sorry
    trimmed := sorry
  }
  dμ_real_zero := sorry
 }

def DRand.bind (x : DRand X) (f : X → Rand Y) : DRand Y := {
  dμPos := erase {
    measureOf := fun A => ∫⁻ x', (f x').μ A ∂x.dμPos
    empty := sorry
    m_iUnion := sorry
    mono := sorry
    iUnion_nat := sorry
    trimmed := sorry
  }
  dμNeg := erase {
    measureOf := fun A => ∫⁻ x', (f x').μ A ∂x.dμNeg
    empty := sorry
    m_iUnion := sorry
    mono := sorry
    iUnion_nat := sorry
    trimmed := sorry
  }
  dμ_real_zero := sorry
}

def Rand.dbind (x : Rand X) (f : X → DRand Y) : DRand Y := {
  dμPos := erase {
    measureOf := fun A => ∫⁻ x', (f x').dμPos A ∂x.μ
    empty := sorry
    m_iUnion := sorry
    mono := sorry
    iUnion_nat := sorry
    trimmed := sorry
  }
  dμNeg := erase {
    measureOf := fun A => ∫⁻ x', (f x').dμNeg A ∂x.μ
    empty := sorry
    m_iUnion := sorry
    mono := sorry
    iUnion_nat := sorry
    trimmed := sorry
  }
  dμ_real_zero := sorry
}


def bind₂ (x : Rand X × DRand X) (f : X → Rand Y × DRand Y) : Rand Y × DRand Y := 
  (x.1.bind fun x' => (f x').1, 
   (x.2.bind fun x' => (f x').1) + (x.1.dbind fun x' => (f x').2))




macro "let" x:Lean.Parser.Term.funBinder " ~~ " y:term:max Lean.Parser.semicolonOrLinebreak z:term : term => `(bind₂ $y (fun $x => $z))

@[app_unexpander bind₂] def unexpandBind₂ : Lean.PrettyPrinter.Unexpander

  | `($(_) $mx:term $f) => 
    match f.raw with
    | `(fun $x:term => $b:term) => do
        let s ← `(let $x ~~ $mx; $b)
        pure s.raw -- .semicolonToNewline
    | `($f) => do
        let s ← `(let x ~~ $mx; $f x)
        pure s.raw -- .semicolonToNewline
  | _ => throw ()
