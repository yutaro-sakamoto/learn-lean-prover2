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

variable (m n : Nat)
variable (i j : Int)

#check i + m
#check i + m + j
#check i + m + n

#check Eq
#check @Eq
#check Eq.symm
#check @Eq.symm

#print Eq.symm

#check And
#check And.intro
#check @And.intro

def foo {α : Type u} (x : α) : α := x

#check foo
#check @foo
#print foo

#print propext

namespace universe_example
universe u v w
def compose {α : Type u} {β : Type v} {γ : Type w}
    (g :β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
end universe_example

def compose2.{u, v, w}
  {α : Type u} {β : Type v} {γ : Type w}
    (g :β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def compose3 (g : β → γ) (f : α → β)(x : α) : γ :=
  g (f x)

#check @compose3

namespace ex2
def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

def id3 : {α : Type} → α → α :=
  @fun α x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

def id5 : {α : Type} → α → α :=
  fun {α} x => id1 x
end ex2

#check (· + 1)
#check (2 - ·)
#eval [1, 2, 3, 4, 5].foldl (·*·) 1
def f (x y z : Nat) :=
  x + y + z
#check (f · 1 ·)
#eval [(1, 2), (3, 4), (5, 6)].map (·.1)

#check (Prod.mk · (· + 1))

def sum (xs : List Nat) :=
  xs.foldl (init := 0) (· + ·)

#eval sum [1, 2, 3, 4, 5]

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
  : p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁

example {a b : Nat} {p : Nat → Nat → Nat → Prop} (h₁ : p a b b) (h₂ : b = a)
  : p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁

def ff (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
  x + y + w - z

example (x z : Nat) : ff (z := z) x = x + 1 + 2 - z := rfl
example (x z : Nat) : ff x (z := z) = x + 1 + 2 - z := rfl
example (x y : Nat) :ff x y = fun z => x + y + 2 - z := rfl
example : ff = (fun x z => x + 3 - z) := rfl
example (x : Nat) : ff x = fun z => x + 3 - z := rfl
example (y : Nat) : ff (y := 5) = fun x z => x + 5 + 2 - z := rfl
def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none => a + c
  | some b => a + b + c

variable {α} [Add α]

example : g = fun (a c : α) => a + c := rfl
example (x : α) : g (c := x) = fun (a : α) => a + x := rfl
example (x : α) : g (b? := some x) = fun (a c :α) => a + x + c := rfl
example (x : α) : g x = fun (c : α) => x + c := rfl
example (x y : α) : g x y = fun (c : α) => x + y + c := rfl

inductive Term where
  | var (name : String)
  | num (val : Nat)
  | app (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none

example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc _ _ _)

example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)
