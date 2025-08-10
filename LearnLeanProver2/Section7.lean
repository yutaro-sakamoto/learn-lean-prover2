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

set_option pp.all true
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
