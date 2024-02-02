
# Probabilistic programming in Lean 4
    
Experiment in writing probabilistic programs in Lean and proving their properties. 

For example a simple program that throws a dice and throws again on six.
```
def throwDice : Rand ℕ :=
  let n ~ (randNat 1 6)
  if n ≠ 6 then
    n
  else
    let m ~ (randNat 1 6)
    n + m
```

`throwDice` is a random variable and we can compute its probability density function with respect to the counting measure on natural numbers.

```
#check throwDice2.pdf' .count
  rewrite_by
    simp[throwDice1,-Finset.sum_boole]
```
which returns
```
fun y ↦
    1/6 * ∑ n in Icc 1 6,
      if n = 6 then
        1/6 * ∑ n_1 in Icc 1 6, if n + n_1 = y then 1 else 0
      else
        if n = y then 1 else 0
```

## Installation and build instructions

To install Lean follow the [manual](https://lean-lang.org/lean4/doc/quickstart.html). Then run these commands

```
git clone https://github.com/lecopivo/Probly.git
cd Probly
lake exe cache get
lake build
```
