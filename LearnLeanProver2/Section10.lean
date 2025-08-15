structure MyAdd (a : Type) where
  add : a → a → a

#check @Add.add

def double (s : MyAdd a) (x : a) : a :=
  s.add x x

#eval double { add := Nat.add } 10
#eval double { add := Nat.mul } 10
#eval double { add := Int.mul } 10

class MyAdd2 (a : Type) where
  add : a → a → a

#check @MyAdd2.add

instance : MyAdd2 Nat where
  add := Nat.add

instance : MyAdd2 Int where
  add := Int.add

instance : MyAdd2 Float where
  add := Float.add

def double2 [MyAdd2 a] (x : a) :a :=
  MyAdd2.add x x

#check @double2
#eval double2 10
#eval double2 (10 : Int)
#eval double2 (10 : Float)
#eval double2 (1.2 + 1)

instance [Add a] : Add (Array a) where
  add x y := Array.zipWith (· + ·) x y

#eval Add.add #[1, 2] #[3, 4]
#eval #[1, 2] + #[3, 4]

class MyInhabited (a : Type u) where
  default : a

instance : MyInhabited Bool where
  default := true

instance : MyInhabited Nat where
  default := 0

instance : MyInhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (MyInhabited.default : Nat)
#eval (MyInhabited.default : Bool)

--export MyInhabited (default)

#eval (default : Nat)
#eval (default : Bool)

instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : Nat × Bool)

instance [Inhabited b] : Inhabited (a → b) where
  default := fun _ => default

#check (inferInstance : Inhabited Nat)

def foo : Inhabited (Nat × Nat) :=
  inferInstance

#eval foo.default

theorem ex : foo.default = (default, default) := rfl

#print inferInstance

structure Person where
  name : String
  age: Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person }
#eval toString ({ name := "Leo", age := 542 : Person }, "hello")

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance instOfNatRational (n : Nat) : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational)

#check (@OfNat.ofNat Nat 2 (instOfNatNat 2))
#check (@OfNat.ofNat Rational 2 (instOfNatRational 2))
#check nat_lit 2

class Monoid (α : Type u) where
  unit : α
  op : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1

#check_failure (inferInstance : Inhabited (Nat × _))

class MyHMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

instance : MyHMul Nat Nat Nat where
  hMul := Nat.mul

export MyHMul (hMul)

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3
--#eval hMul 4 #[2, 3, 4]

@[default_instance]
instance : MyHMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)
#eval (fun y => xs.map (fun x => hMul x y)) 3

structure Point where
  x : Nat
  y : Nat

section

local instance : Add Point where
  add a b := { x:= a.x + b.x, y := a.y + b.y }

def double3 (p : Point) :=
  p + p

end

instance addPoint : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double4 (p : Point) := p + p

attribute [-instance] addPoint

namespace Point
scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double4 (p : Point) := p + p
end Point

#check @instDecidableAnd

def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

#print step

example : 10 < 5 ∨ 1 > 0 := by decide
example : ¬ ( True ∧ False) := by decide
example : 10 * 20 = 200 := by decide
theorem ex2 : True ∧ 2 = 1 + 1 := by decide
#print ex2
#check @of_decide_eq_true
#check @decide

def foo2 : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance

#check (inferInstance : Add Nat)

#check inferInstanceAs (Add Nat)
#check @inferInstanceAs

def Set (α : Type u) := α → Prop

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))

example : Inhabited (Set α) :=
  inferInstance

class Foo where
  a : Nat
  b : Nat

instance (priority := default + 1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 := rfl

instance (priority := default + 2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 := rfl

instance : Coe Bool Prop where
  coe b := b = true

#eval if true then 5 else 3
#eval if false then 5 else 3


--def List.toSet : List α → Set α = fun _ => Set.empty
--instance : Coe (List α) (Set α) where
--  coe a := a.toSet

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b

#check Semigroup.carrier

instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier

example (S: Semigroup) (a b c : S):  (a * b) * c = a * (b * c) :=
  Semigroup.mul_assoc _ a b c

structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)

instance (S1 S2 : Semigroup) : CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where
  coe m := m.mor

theorem resp_mul {S1 S2 : Semigroup} (f : Morphism S1 S2) (a b : S1)
    : f (a * b) = f a * f b :=
  f.resp_mul a b

example (S1 S2 : Semigroup) (f : Morphism S1 S2) (a: S1)
    : f (a * a * a) = f a * f a * f a :=
  calc f (a * a * a)
  _ = f (a * a) * f a := by rw [resp_mul]
  _ = f a * f a * f a := by rw [resp_mul]
