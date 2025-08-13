open Nat

def sub1 : Nat → Nat
  | zero => zero
  | succ x => x

def isZero : Nat → Bool
  | zero => true
  | succ _ => false

example : sub1 0 = 0 := rfl
example (x : Nat) : sub1 (succ x) = x := rfl

example : isZero 0 = true := rfl
example (x : Nat) : isZero (succ x) = false := rfl

example : sub1 7 = 6 := rfl
example (x : Nat) : isZero (x + 3) = false := rfl

def sub2 : Nat → Nat
  | 0 => 0
  | x + 1 => x

def isZero2 : Nat → Bool
  | 0 => true
  | _ + 1 => false

def swap : α × β → β × α
  | (a, b) => (b, a)

def foo : Nat × Nat → Nat
  | (m, n) => m + n

def bar : Option Nat → Nat
  | some n => n + 1
  | none => 0

namespace Hidden
def not : Bool → Bool
  | true => false
  | false => true

def not_not : ∀ (b : Bool), not (not b) = b
  | true => rfl
  | false => rfl

def not_not' : ∀ (b : Bool), not (not b) = b
  | true => rfl
  | false => rfl
end Hidden

example (p q : Prop) : p ∧ q → q ∧ p
  | And.intro h₁ h₂ => And.intro h₂ h₁

example (p q : Prop) : p ∨ q → q ∨ p
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq

def sub22 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | x + 2 => x

example : sub22 0 = 0 := rfl
example : sub22 1 = 0 := rfl
example : sub22 (x+2) = x := rfl
example : sub22 5 = 3 := rfl

example (p q : α → Prop)
    : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
  | Exists.intro x (Or.inl px) => Or.inl (Exists.intro x px)
  | Exists.intro x (Or.inr qx) => Or.inr (Exists.intro x qx)

example (p q : α → Prop)
    : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
  | ⟨x, Or.inl px⟩ => Or.inl ⟨x, px⟩
  | ⟨x, Or.inr qx⟩ => Or.inr ⟨x, qx⟩

def foo2 : Nat × Nat → Nat
  | (0, _) => 0
  | (_ + 1, 0) => 1
  | (_ + 1, _ + 1) => 2

def foo3 : Nat → Nat → Nat
  | 0, _ => 0
  | _ + 1, 0 => 1
  | _ + 1, _ + 1 => 2

def bar2 : List Nat → List Nat → Nat
  | [], [] => 0
  | a :: _, [] => a
  | [], b :: _ => b
  | a :: _, b :: _ => a + b

def and : Bool → Bool → Bool
  | true, a => a
  | false, _ => false

def or : Bool → Bool → Bool
  | true, _ => true
  | false, a => a

def cond2 : Bool → α → α → α
  | true, x, _ => x
  | false, _, y => y

def tail1 {α : Type u} : List α → List α
  | [] => []
  | _ :: as => as

def tail2 : {α : Type u} → List α → List α
  | _, [] => []
  | _, _ :: as => as

def foo4 : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2

example : foo4 0 0 = 0 := rfl
example : foo4 0 (n+1) = 0 := rfl
example : foo4 (m+1) 0 = 1 := rfl
example : foo4 (m+1) (n+1) = 2 := rfl

def f1 : Nat → Nat → Nat
  | 0, _ => 1
  | _, 0 => 2
  | _, _ => default

example : f1 0 0 = 1 := rfl
example : f1 0 (a+1) = 1 := rfl
example : f1 (a+1) 0 = 2 := rfl
example : f1 (a + 1) (b + 1) = default := rfl

def f2 : Nat → Nat → Option Nat
  | 0, _ => some 1
  | _, 0 => some 2
  | _, _ => none

example : f2 0 0 = some 1 := rfl
example : f2 0 (a+1) = some 1 := rfl
example : f2 (a+1) 0 = some 2 := rfl
example : f2 (a+1) (b+1) = none := rfl

def bar3 : Nat → List Nat → Bool → Nat
  | 0,   _,      false => 0
  | 0,   b :: _, _     => b
  | 0,   [],     true  => 7
  | a+1, [],     false => a
  | a+1, [],     true  => a + 1
  | a+1, b :: _, _     => a + b

def foo5 : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _ => 3

#print foo.match_1

def add : Nat → Nat → Nat
  | m, zero => m
  | m, succ n => succ (add m n)

theorem add_zero (m : Nat) : add m zero = m := rfl
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := rfl

theorem zero_add : ∀ n, add zero n = n
  | zero => rfl
  | succ n => congrArg succ (zero_add n)

def mul : Nat → Nat → Nat
  | _, zero => zero
  | n, succ m => add (mul n m) n

theorem mul_zero (m : Nat) : mul m zero = zero := rfl
theorem mul_succ (m n : Nat) : mul m (succ n) = add (mul m n) m := rfl

theorem zero_add2 : ∀ n, add zero n = n
  | zero => rfl
  | succ n => by simp [add, zero_add2]

def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example : fib (n + 2) = fib (n + 1) + fib n := rfl

example : fib 7 = 21 := rfl

def fast_fib' (n₁ n₂ n : Nat) : Nat :=
  match n with
  | 0 => n₁ + n₂
  | succ n => fast_fib' n₂ (n₁ + n₂) n

def fast_fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | (n + 2) => fast_fib' 1 1 n

theorem fast_fib'_is_fib : fast_fib = fib := by
  funext n
  cases n with
  | zero => rfl
  | succ zero => sorry

def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0 => (0, 1)
    | n + 1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100

def fibFast2 (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0 => (0, 1)
    | n + 1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2

variable (C : Nat → Type u)
#check (@Nat.below C : Nat → Type u)
#reduce @Nat.below C (3 : Nat)
#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)

def append : List α → List α → List α
  | [], bs => bs
  | a::as, bs => a :: append as bs

example : append [1, 2, 3] [4, 5] = [1, 2 ,3 , 4 ,5] := rfl

def listAdd [Add α] : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | a :: as , b :: bs => (a + b) :: listAdd as bs

#eval listAdd [1, 2, 3] [4,5,6,6,9,10]

def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0, as => as
    | n+1, as => loop n (a::as)
  loop n []

#check @replicate.loop

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0 => simp [replicate.loop]
    | n+1 => simp +arith [replicate.loop, aux n]
  exact aux n []

def replicate2 (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0, as => as
    | n+1, as => loop n (a::as)

theorem length_replicate2 (n : Nat) (a : α) : (replicate2 n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
      : (replicate2.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate2.loop]
    | n+1 => simp +arith [replicate2.loop, aux n]

namespace tmp
variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)
end tmp

mutual
  def even : Nat → Bool
    | 0 => true
    | n + 1 => odd n
  def odd : Nat → Bool
    | 0 => false
    | n + 1 => even n
end

example : even (a + 1) = odd a := by
  simp [even]

example : odd (a + 1) = even a := by
  simp [odd]

theorem even_eq_not_odd : ∀ a, even a = not (odd a) := by
  intro a; induction a
  . simp [even, odd]
  . simp [even, odd, *]

mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : ∀ n, Odd n -> Even (n + 1)
  inductive Odd : Nat → Prop where
    | odd_succ : ∀ n, Even n → Odd (n + 1)
end

open Even Odd
theorem not_odd_odd_zero : ¬ Odd 0 :=
  fun h => nomatch h

theorem even_of_odd_succ : ∀ n, Odd (n + 1) → Even n
  | _, odd_succ n h => h

theorem odd_of_even_succ : ∀ n, Even (n + 1) → Odd n
  | _, even_succ n h => h

#check odd_succ
#check even_succ
#check odd_of_even_succ

inductive Term where
  | const : String → Term
  | app : String → List Term → Term

namespace Term

mutual
  def numConsts : Term → Nat
    | const _ => 1
    | app _ cs => numConstsLst cs
  def numConstsLst : List Term → Nat
    | [] => 0
    | c :: cs => numConsts c + numConstsLst cs
end

def sample := app "f" [app "g" [const "x"], const "y"]
def sample2 := [app "g" [const "x", const "y"], const "y"]

#eval numConsts sample
#eval numConstsLst sample2

mutual
  def replaceConst (a b : String) : Term → Term
    | const c => if a == c then const b else const c
    | app f cs => app f (replaceConstLst a b cs)
  def replaceConstLst (a b : String) : List Term → List Term
    | [] => []
    | c :: cs => replaceConst a b c :: replaceConstLst a b cs
end

mutual
  theorem numConsts_replaceConst (a b : String) (e : Term)
      : numConsts (replaceConst a b e) = numConsts e := by
    match e with
    | const c => simp [replaceConst]; split <;> simp [numConsts]
    | app f cs => simp [replaceConst, numConsts, numConsts_replaceConstLst a b cs]
  theorem numConsts_replaceConstLst (a b : String) (es : List Term)
      : numConstsLst (replaceConstLst a b es) = numConstsLst es := by
    match es with
    | [] => simp [replaceConstLst, numConstsLst]
    | c :: cs =>
      simp [replaceConstLst, numConstsLst, numConsts_replaceConst a b c,
        numConsts_replaceConstLst a b cs]
end
end Term

inductive MyVector (α : Type u) : Nat → Type u
  | nil : MyVector α 0
  | cons : α → {n : Nat} → MyVector α n → MyVector α (n + 1)

namespace MyVector
#check @MyVector.casesOn

def tailAux (v : MyVector α m) : m = n + 1 → MyVector α n :=
  MyVector.casesOn (motive := fun x _ => x = n + 1 → MyVector α n) v
  (fun h : 0 = n + 1 => Nat.noConfusion h)
  (fun (a : α) (m : Nat) (as : MyVector α m) =>
   fun (h : m + 1 = n + 1) =>
    Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : MyVector α (n + 1)) : MyVector α n :=
  tailAux v rfl

def add [Add α] : {n : Nat} → MyVector α n → MyVector α n → MyVector α n
  | 0, nil, nil => nil
  | _ + 1, cons a as, cons b bs => cons (a + b) (add as bs)

def add2 [Add α] : {n : Nat} → MyVector α n → MyVector α n → MyVector α n
  | .(_), nil, nil => nil
  | .(_), cons a as, cons b bs => cons (a + b) (add as bs)

def add3 [Add α] : {n : Nat} → MyVector α n → MyVector α n → MyVector α n
  | _, nil, nil => nil
  | _, cons a as, cons b bs => cons (a + b) (add as bs)

end MyVector

inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a

def isNotZero (m : Nat) : Bool :=
  match m with
  | 0 => false
  | _+1 => true

def myfilter (p : α → Bool) : List α → List α
  | [] => []
  | a :: as =>
    match p a with
    | true => a :: myfilter p as
    | false => myfilter p as

def foo6 (n : Nat) (b c : Bool) :=
  5 + match n - 5, b && c with
      | 0,   true  => 0
      | m+1, true  => m + 7
      | 0,   false => 5
      | m+1, false => m + 3

#eval foo6 7 true false

example : foo6 7 true false = 9 := rfl

def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n

def bar₂ (p : Nat × Nat) : Nat :=
  match p with
  | (m, n) => m + n

def bar₃ : Nat × Nat → Nat :=
  fun (m, n) => m + n

def bar₄ (p : Nat × Nat) : Nat :=
  let (m, n) := p; m + n

section
  variable (p q : Nat → Prop)

  example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
    | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

  example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
      : ∃ x y, p x ∧ q y :=
    match h₀, h₁ with
    | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

  example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
    fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, px, qy⟩

  example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
      : ∃ x y, p x ∧ q y :=
    let ⟨x, px⟩ := h₀
    let ⟨y, qy⟩ := h₁
    ⟨x, y, px, qy⟩
end
