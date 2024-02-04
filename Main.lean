import Probly.Basic
import Probly.Dice

open Probly

def main : IO Unit := do

  let mut score : Array Nat := Array.mkArray 12 0
  
  for _ in [0:1000000] do
    let n ← throwDice1.get
    let n := n-1
    score := score.set! n (score[n]! + 1)
  
  IO.println score

