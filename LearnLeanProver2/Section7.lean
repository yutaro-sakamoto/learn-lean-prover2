inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
  deriving Repr

#check Weekday.sunday
#check Weekday.monday

inductive Weekday2 where
  | sunday2
  | monday2
  | tuesday2
  | wednesday2
  | thursday2
  | friday2
  | saturday2

open Weekday
def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday => 1
  | monday => 2
  | tuesday => 3
  | wednesday => 4
  | thursday => 5
  | friday => 6
  | saturday => 7

#eval numberOfDay Weekday.sunday
#eval numberOfDay Weekday.monday
#eval numberOfDay tuesday

--set_option pp.all true
#print numberOfDay
--#print numberOfDay.match_1
#print Weekday.casesOn
#check @Weekday.rec

#eval tuesday

def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)
#eval next (previous tuesday)

example : ∀ (d : Weekday), d = next (previous d) :=
  fun d =>
  match d with
  | sunday => show sunday = next (previous sunday) from rfl
  | monday => show monday = next (previous monday) from rfl
  | tuesday => show tuesday = next (previous tuesday) from rfl
  | wednesday => show wednesday = next (previous wednesday) from rfl
  | thursday => show thursday = next (previous thursday) from rfl
  | friday => show friday = next (previous friday) from rfl
  | saturday => show saturday = next (previous saturday) from rfl


example : ∀ (d : Weekday), d = next (previous d) := by
  intro d
  cases d
  all_goals rfl

example : ∀ (d : Weekday), d = next (previous d) := by
  intro d
  cases d <;> rfl

def and (a b : Bool) : Bool :=
  match a with
  | true => b
  | false => false

def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b

def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (2 * ·)
    (2 * · + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)

def sum_example2 (s : Sum Nat Nat) : Nat :=
  match s with
    | Sum.inl a => 2 * a
    | Sum.inr b => 2 * b + 1

#eval sum_example2 (Sum.inl 3)
#eval sum_example2 (Sum.inr 3)

structure Color where
  (red: Nat) (green : Nat) (blue : Nat)
  deriving Repr

def yellow := Color.mk 255 255 0

#print Color.red
#eval Color.red yellow

def partial_function (α : Type u) (β : Type v) := α → Option β

def compose_partial_functions (g : partial_function β γ) (f : partial_function α β)
    : partial_function α γ :=
  fun x =>
  match f x with
  | none => none
  | some y => g y

theorem assoc_compose_parital_function
  {α : Type u1}
  {β : Type u2}
  {γ : Type u3}
  {δ : Type u4}
  (h : partial_function γ δ)
  (g : partial_function β γ)
  (f : partial_function α β) :
  compose_partial_functions h (compose_partial_functions g f) = compose_partial_functions (compose_partial_functions h g) f := by
  funext x
  simp [compose_partial_functions]
  cases f x with
  | none => rfl
  | some y =>
    cases g y with
    | none => rfl
    | some z => rfl

example
  (h : partial_function γ δ)
  (g : partial_function β γ)
  (f : partial_function α β) :
  compose_partial_functions h (compose_partial_functions g f) = compose_partial_functions (compose_partial_functions h g) f := by
  funext x
  simp [compose_partial_functions]
  cases f x with
  | none => rfl
  | some y =>
    cases g y
    all_goals rfl

def injective (f : α → β) := ∀ x : α, ∀ y : α, (f x = f y → x = y)

example (g : β → γ) (f : α → β)
    : injective g ∧ injective f → injective (g ∘ f) := by
  intro ⟨hg, hf⟩
  intro x y
  intro h
  apply hf
  apply hg
  exact h

#check @Nat.rec

theorem add_zero (m : Nat) : m + 0 = m := rfl

open Nat

theorem my_add_succ (m n : Nat) : m + Nat.succ n = Nat.succ (m + n) := rfl
theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x)
   n
   (show 0 + 0 = 0 from rfl)
   (fun (n : Nat) (ih : 0 + n = n) =>
    show 0 + succ n = succ n from
    calc 0 + succ n
      _ = succ (0 + n) := rfl
      _ = succ n       := by rw [ih])

theorem zero_add_induction_step (n : Nat) (ih : 0 + n = n) : 0 + succ n = succ n := by
  rw [my_add_succ, ih]

example (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
  rfl
  zero_add_induction_step

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k (ih : m + n + k = m + (n + k)) =>
      show m + n + succ k = m + (n + succ k) from
      calc m + n + succ k
      _ = succ (m + n + k) := rfl
      _ = succ (m + (n + k)) := by rw [ih]
      _ = m + succ (n + k) := rfl
      _ = m + (n + succ k) := rfl
    )

theorem add_assoc_step {m n : Nat} (k : Nat) (ih : m + n + k = m + (n + k))
    : m + n + Nat.succ k = m + (n + Nat.succ k) := by
  rw [my_add_succ]
  rw [ih]
  rw [←my_add_succ]
  rw [←my_add_succ]

theorem add_assoc2 (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
  rfl
  add_assoc_step

theorem add_assoc3 (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    rfl
    (fun k ih => by simp [add_succ (m + n) k, ih]; rfl)

theorem my_succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    (show succ n + 0 = succ (n + 0) from rfl)
    (fun (m : Nat) (ih : succ n + m = succ (n + m)) =>
     show succ n + succ m = succ (n + succ m) from
     calc succ n + succ m
       _ = succ (succ n + m)   := rfl
       _ = succ (succ (n + m)) := by rw [ih]
       _ = succ (n + succ m)   := rfl)

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
   (show m + 0 = 0 + m by rw [Nat.zero_add, Nat.add_zero])
   (fun (n : Nat) (ih : m + n = n + m) =>
    show m + succ n = succ n + m from
    calc m + succ n
      _ = succ (m + n) := rfl
      _ = succ (n + m) := by rw [ih]
      _ = succ n + m   := by rw [my_succ_add])

theorem my_succ_add2 (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    rfl
    (fun m ih => by simp only [add_succ, ih])

open List
def append (as bs : List α) : List α :=
  match as with
  | nil => bs
  | cons a as => cons a (append as bs)

theorem my_nil_append (as : List α) : append nil as = as :=
  rfl

theorem my_cons_append (a : α) (as bs : List α)
    : append (cons a as) bs = cons a (append as bs) :=
  rfl

theorem my_append_nil (as : List α) : append as nil = as :=
  match as with
  | nil => rfl
  | cons a as =>
    show append (cons a as) nil = cons a as from
    calc append (cons a as) nil
      _ = cons a (append as nil) := my_cons_append a as nil
      _ = cons a as              := by rw [my_append_nil as]

example (as : List α) : append as nil = as := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [my_cons_append a as nil, ih]

theorem append_assoc (as bs cs : List α)
    : append (append as bs) cs = append as (append bs cs) :=
  match as with
  | nil => rfl
    --show append (append nil bs) cs = append nil (append bs cs) from
    --calc append (append nil bs) cs
    --  _ = append bs cs := by rw [my_nil_append bs]
    --  _ = append nil (append bs cs) := my_nil_append (append bs cs)
  | cons a as =>
    --show append (append (cons a as) bs) cs = append (cons a as) (append bs cs) from
    --calc append (append (cons a as) bs) cs
    --  _ = append (cons a (append as bs)) cs := by rw [my_cons_append]
    --  _ = cons a (append (append as bs) cs) := by rw [my_cons_append]
    --  _ = cons a (append as (append bs cs)) := by rw [append_assoc as bs cs]
    --  _ = append (cons a as) (append bs cs) := by rw [my_cons_append]
    by simp [my_cons_append, append_assoc]

example (as bs cs : List α)
    : append (append as bs) cs = append as (append bs cs) :=
  by induction as with
  | nil => rfl
  | cons a as ih => simp [my_cons_append, ih]
