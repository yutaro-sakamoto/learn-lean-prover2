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
