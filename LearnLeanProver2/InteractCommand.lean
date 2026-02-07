import Lean.Elab.Command

#check_failure 1 + "hello"
#check_failure (by rfl : 1 = 2)
#check_failure (by contradiction : 1 + 4 = 5)

#check 'a'
#check "hello"
#check 1
#check 1.0
#check -1
#check (1: Int)
#check [1, 2, 4]
#check #[1, 2, 3]
#check fun x => x + 42
#check true
#check True

#eval 1 + 1

def fac : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fac n

#eval fac 5
