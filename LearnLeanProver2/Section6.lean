section
variable (x y : Nat)
def double := x + x

#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]
end

namespace Foo
def bar : Nat := 1
end Foo
open Foo
#check bar
#check Foo.bar

def Foo.bar2 : Nat := 1

def String.add (a b : String) : String :=
  a ++ b

def Bool.add(a b : Bool) : Bool :=
  a != b

open Bool
open String
--#check add
#check String.add
#check Bool.add
--#check _root_.add

#check add "hello" "world"
#check add true false
--#check add Nat Nat

protected def Foo.bar3 : Nat := 1

open Foo
#check Foo.bar

section open_1
open Nat (succ zero gcd)
#check zero
#eval gcd 15 6
end open_1

section open_hiding
open Nat hiding succ gcd
#check zero
--#eval gcd 15 6
#eval Nat.gcd 15 6
end open_hiding

section open_3
open Nat renaming mul → times, add → plus
#eval plus (times 2 2) 3
#eval Nat.mul 2 2
end open_3

namespace Foo
export And(intro left right)
#check And.intro
#check Foo.intro
#check intro
#check left
end Foo

export And(intro left right)
#check intro

def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

@[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

@[simp] theorem List.isPrefix_self2 (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [simp] List.isPrefix_self2

def instLe : LE (List α) :=
  { le := isPrefix }
section
attribute [local instance] instLe
example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩
end

def reflexive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ (a : α), r a a

def symmetric {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b : α}, r a b → r b a

def transitive {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r b c → r a c

def euclidean {α : Type u} (r : α → α → Prop) : Prop :=
  ∀ {a b c : α}, r a b → r a c → r b c

theorem th1 {α : Type u} {r : α → α → Prop}
    (reflr : reflexive r) (euclr : euclidean r)
    : symmetric r :=
  fun {a b : α} =>
  fun (h : r a b) =>
  show r b a from euclr h (reflr a)

theorem th2 {α : Type u} {r : α → α → Prop}
    (symmr : symmetric r) (euclr : euclidean r)
    : transitive r :=
  fun {a b c : α} =>
  fun (rab : r a b) (rbc : r b c) =>
  show r a c from euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
    (reflr : reflexive r) (euclr : euclidean r)
    : transitive r :=
  th2 (th1 reflr @euclr) @euclr

variable (r : α → α → Prop)
variable (euclr : euclidean r)

#check @euclr
#check euclr
