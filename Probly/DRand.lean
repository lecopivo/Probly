import Mathlib.MeasureTheory.Measure.VectorMeasure

import Probly.Basic


open MeasureTheory ENNReal BigOperators Finset

namespace Probly

structure DRand (X : Type) [MeasurableSpace X] where
  dμPos : Erased (Measure X)
  dμNeg : Erased (Measure X)
  finite_pos : IsFiniteMeasure dμPos.out
  finite_neg : IsFiniteMeasure dμNeg.out
  dμ_real_zero : dμPos.out ⊤ = dμNeg.out ⊤
  -- drand : R → _root_.Rand X -- R should have [RealScalar R]

register_simp_attr rand_simp

variable {X Y} [MeasurableSpace X] [MeasurableSpace Y]

instance (x : DRand X) : IsFiniteMeasure (x.dμPos.out) := x.finite_pos
instance (x : DRand X) : IsFiniteMeasure (x.dμNeg.out) := x.finite_neg

instance : Zero (DRand X) := sorry
instance : Add (DRand X) := sorry
instance : SMul ℝ (DRand X) := sorry


def DRand.pure (x : X) : DRand X := {  
  dμPos := erase {
    measureOf := Measure.dirac x
    empty := sorry
    m_iUnion := sorry
    mono := sorry
    iUnion_nat := sorry
    trimmed := sorry
  }
  dμNeg := erase {
    measureOf := sorry -- (1 : Measure X) - Measure.dirac x
    empty := sorry
    m_iUnion := sorry
    mono := sorry
    iUnion_nat := sorry
    trimmed := sorry
  }
  finite_pos := sorry
  finite_neg := sorry
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
  finite_pos := sorry
  finite_neg := sorry
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
  finite_pos := sorry
  finite_neg := sorry
  dμ_real_zero := sorry
}
