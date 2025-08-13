structure Point (α : Type u) where
  mk :: (x : α) (y : α)

#check Point
#check @Point.rec
#check @Point.mk
#check @Point.x
#check @Point.y

structure Point2 (α : Type u) where
  x : α
  y : α

#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)

example (a b : α) : Point2.x (Point2.mk a b) = a := rfl
example (a b : α) : Point2.y (Point2.mk a b) = b := rfl

def p := Point2.mk 10 20

#check p.x
#eval p.x
#eval p.y

structure Point3 (α : Type u) where
  x : α
  y : α
  deriving Repr

def Point3.add (p q : Point3 Nat) :=
  Point3.mk (p.x + q.x) (p.y + q.y)

def pp : Point3 Nat := Point3.mk 1 2
def qq : Point3 Nat := Point3.mk 3 4

#eval pp.add qq

def Point3.smul (p : Point Nat) (n : Nat) :=
  Point3.mk (n * p.x) (n * p.y)

def p1 : Point3 Nat := Point3.mk 1 2

--#eval p1.smul 3

#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

#eval xs.map f

structure Point4 (α : Type u) where
  x : α
  y : α

#check { x := 10, y := 20 : Point Nat }
#check { y := 20, x := 10 : Point _ }
#check ( {x := 10, y := 20 } : Point Nat)

example : Point Nat :=
  { y := 20, x := 10 }

structure MyStruct where
  {α : Type u}
  {β : Type v}
  a : α
  b : β

#check { a := 10, b := true : MyStruct }

structure Point5 (α : Type u) where
  x : α
  y : α
  deriving Repr

def p4 : Point5 Nat :=
  { x := 1, y := 2 }

#eval { p4 with y := 3 }
#eval { p4 with x := 4 }

structure Point6 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point6 Nat :=
  { x := 5, y := 5, z := 5 }

def r : Point6 Nat :=
  { p4, q with x := 6 }

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl

structure Point7 (α : Type u) where
  x : α
  y : α

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color

structure Point8 (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point8 α, RGBValue where
  no_blue : blue = 0

def p5 : Point8 Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint  Nat :=
  { p5 with red := 200, green := 40, blue := 0, no_blue := rfl}

example : rgp.x = 10 := rfl
example : rgp.red = 200 := rfl
