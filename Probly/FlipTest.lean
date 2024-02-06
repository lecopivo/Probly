import Probly.Flip

open MeasureTheory ENNReal BigOperators Finset

namespace Probly

noncomputable
def test (θ : ℝ) : Rand ℝ :=
  let b ~ (flip θ)
  if b then
    Rand.pure 0
  else
    Rand.pure (-θ/2)



variable (θ : ℝ)


#check (randFwdDeriv test θ 1)
  rewrite_by
  unfold test
  simp (disch:=sorry) only [rand_simp]

theorem push_to_if {c} [Decidable c] (f : α → β) (a a' : α) :
    f (if c then a else a') = if c then f a else f a' := sorry


#check (randFwdDeriv test θ 1).dval.expectedValueChange id
  rewrite_by
  unfold test
  simp (disch:=sorry) only [rand_simp]
  simp only [FDRand.bind, FDRand.dpure,rand_simp]

  simp only [push_to_if FDRand.val,
             push_to_if FDRand.dval,
             push_to_if (DRand.action · id),
             ← push_to_if Rand.pure,
             rand_simp,ite_true,ite_false,dflip]

  simp [id,rand_simp,Rand.expectedValue]


variable (φ : ℝ → ℝ)


-- set_option trace.Meta.Tactic.simp.discharge true in
-- set_option trace.Meta.Tactic.simp.unify true in
#check (randFwdDeriv test θ 1).dval.expectedValueChange φ
  rewrite_by
  unfold test
  simp (disch:=sorry) only [rand_simp]
  simp only [FDRand.bind, FDRand.dpure, rand_simp]

  conv => 
    enter [2]
    enter [2,x']
    simp only [push_to_if FDRand.dval]
    simp only [push_to_if (DRand.action · φ),rand_simp]

  conv => 
    enter [1]
    simp only [push_to_if FDRand.val]
    simp only [rand_simp,id,dflip]
    simp only [ite_true, ite_false,rand_simp]
    simp only [erase_out]
  
  

noncomputable
def _root_.Bool.toReal (b : Bool) : ℝ := if b then 1 else 0


noncomputable
def test2 (θ : ℝ) : Rand ℝ :=
  let b ~ (flip θ)
  if b then
    Rand.pure 0
  else
    let b' ~ (flip θ)
    if b' then
      Rand.pure (4*θ)
    else
      Rand.pure (-θ/2)



#check (randFwdDeriv test2 θ 1).dval.expectedValueChange φ
  rewrite_by
  unfold test2
  simp (disch:=sorry) only [rand_simp]
  simp only [FDRand.bind, FDRand.dpure, rand_simp]

  simp only [push_to_if FDRand.val,
             push_to_if FDRand.dval,
             push_to_if (DRand.action · φ),
             ← push_to_if Rand.pure,
             rand_simp,ite_true,ite_false,dflip]

  simp only [expectedValue_to_bind]




#check (test θ).pdf' .count
  rewrite_by
    unfold test
    simp [rand_simp,flip]
    enter[y]
    
