import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Probability.Density
import Mathlib.Control.Random


open MeasureTheory

structure Erased (α : Type) : Type where
  spec : α → Prop
  ex : ∃ a, spec a
  uniq : ∀ a b, spec a → spec b → a = b

@[coe]
noncomputable
def Erased.get (x : Erased α) : α := Classical.choose x.ex

def Erased.erase (x : α) : Erased α where
  spec := Eq x
  ex := ⟨x, rfl⟩
  uniq := by intro a b h h'; rw[← h,h']

@[ext]
theorem Erased.ext (x y : Erased α) : x.get = y.get → x = y := sorry

noncomputable
instance : Coe (Erased α) α where
  coe x := x.get

open ENNReal

noncomputable
instance [MeasurableSpace X] : CoeFun (Erased (Measure X)) (fun _ => Set X → ℝ≥0∞) where
  coe μ A := μ.get A
 
structure Ran (X : Type) [MeasurableSpace X] where
  μ : Erased (Measure X)
  rand : Rand X


def ranNat (lo hi : ℕ) : Ran ℕ where
  μ := .erase Measure.count
  rand := fun g => do
    let g : StdGen := g.down
    let (n,g) := randNat g lo hi
    pure (n, ← ULiftable.up g)
    

variable {X Y} [MeasurableSpace X] [MeasurableSpace Y]

@[ext]
theorem Ran.ext (x y : Ran X) : x.μ = y.μ → x.rand = y.rand → x = y := sorry


def Ran.get (x : Ran X) : IO X := do 
  let stdGen ← ULiftable.up IO.stdGenRef.get
  let (res, new) := x.rand stdGen
  let _ ← ULiftable.up (IO.stdGenRef.set new.down)
  pure res

noncomputable
def Ran.pdf' (x : Ran X) (ν : Measure X := by volume_tac) : X → ℝ≥0∞ :=
  Measure.rnDeriv x.μ ν 

noncomputable
abbrev Ran.pdf {X} [MeasureSpace X] (x : Ran X) : X → ℝ≥0∞ := x.pdf' MeasureSpace.volume


def Ran.pure (x : X) : Ran X where
  μ := .erase (Measure.dirac x)
  rand := Pure.pure x


def Ran.bind (x : Ran X) (f : X → Ran Y) : Ran Y where
  μ := .erase {
    measureOf := fun A => ∫⁻ x', (f x').μ A ∂x.μ
    empty := sorry
    mono := sorry
    iUnion_nat := sorry 
    m_iUnion := sorry
    trimmed := sorry
  }
  rand := do (f (← x.rand)).rand

@[simp]
theorem Erased.erase_get (x : α) : (erase x).get = x := sorry

@[simp]
theorem lower_integral_direc (f : X → ℝ≥0∞) : (∫⁻ x', f x' ∂(Measure.dirac x)) = f x := sorry


@[simp]
theorem bind_pdf (ν : Measure Y) (x : Ran X) (f : X → Ran Y) :
  (x.bind f).pdf' ν = fun y => ∫⁻ x', ((f x').pdf' ν y) ∂x.μ := by funext y; simp[Ran.pdf',Ran.bind,Ran.pure]; sorry

theorem bind_μ_apply (x : Ran X) (f : X → Ran Y) (A : Set Y):
  (x.bind f).μ A = ∫⁻ x', (f x').μ A ∂x.μ := by simp[Ran.bind,Ran.pure];

theorem pure_bind_μ (x : X) (f : X → Ran Y) :
  ((Ran.pure x).bind f).μ.get = (f x).μ := by ext A _; simp[Ran.pure,Ran.bind]

@[simp]
theorem Ran.bind_pure (ν : Measure Y) (x : Ran X) (f : X → Y) :
    (x.bind Ran.pure) = x := by 
  simp[Ran.bind,Ran.pure]; ext 
  . simp; sorry
  . rfl

@[simp]
theorem Ran.pure_bind (x : X) (f : X → Ran Y) :
    (Ran.pure x |>.bind f) = f x := by simp[Ran.bind,Ran.pure]; ext <;> simp


theorem pure_bind_pdf (ν : Measure Y) (x : X) (f : X → Ran Y) :
  ((Ran.pure x).bind f).pdf' ν = (f x).pdf' ν := by simp

theorem bind_pure_μ (x : Ran X) (f : X → Y) :
  (x.bind (fun x' => Ran.pure (f x'))).μ.get = .map f x.μ.get := by sorry


variable (x : Ran ℕ) (A : Set ℕ)

set_option pp.notation false in
set_option pp.coercions false in


macro "let" x:term " ~ " y:term:max linebreak z:term : term => `(Ran.bind $y (fun $x => $z))

instance [MeasurableSpace α]: Coe α (Ran α) := ⟨Ran.pure⟩

def throwDice : Ran ℕ := 
  let n ~ (ranNat 1 6)
  if n ≠ 6 then
    n
  else
    let m ~ (ranNat 1 6)
    n + m

#check Nat

#check ite

@[simp]
theorem pdf_ite (c : Prop) [h : Decidable c] (t e : Ran X) (ν : Measure X) (x : X) :
  Ran.pdf' (if c then t else e) ν x = if c then t.pdf' ν x else e.pdf' ν x := sorry

@[simp]
theorem pdf_pure (n : ℕ) : 
    (Ran.pure n).pdf' Measure.count = fun n' => if n=n' then 1 else 0 := sorry

open BigOperators Finset

@[simp]
theorem ranNat_integral (lo hi : Nat) (f : ℕ → ℝ≥0∞) : 
    ∫⁻ n, f n ∂(ranNat lo hi).μ = (1/(hi-lo+1) : ℝ≥0∞) *∑ n in Icc lo hi, f n := sorry


-- set_option trace.Meta.Tactic.simp.rewrite true in
theorem throwDice_pdf : throwDice.pdf' Measure.count = sorry := by
  conv => 
    lhs
    unfold _root_.throwDice
    simp[-Finset.sum_boole]
  sorry



#eval _root_.throwDice.get


