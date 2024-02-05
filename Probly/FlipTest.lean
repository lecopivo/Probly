import Probly.Flip

namespace Probly

noncomputable
def test (θ : ℝ) : Rand ℝ := 
  let b ~ (flip θ)
  if b then
    Rand.pure 0
  else
    Rand.pure (-θ/2)


set_option trace.Meta.Tactic.simp.discharge true in
set_option trace.Meta.Tactic.simp.unify true in
set_option trace.Meta.Tactic.simp.rewrite true in
#check randFwdDeriv test 
  rewrite_by
  unfold test
  simp (disch:=sorry) only [rand_simp]
