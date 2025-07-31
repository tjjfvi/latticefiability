
structure Lattice where
  T : Type

  le : T -> T -> Prop
  join : T -> T -> T
  meet : T -> T -> T

  refl : {a : T} -> le a a
  trans : {a b c : T} -> le a b -> le b c -> le a c
  antisymm : {a b : T} -> le a b -> le b a -> a = b

  join_upper : {x y : T} -> le x (join x y) ∧ le y (join x y)
  join_least : {x y w : T} -> le x w ∧ le y w -> le (join x y) w

  meet_lower : {x y : T} -> le (meet x y) x ∧ le (meet x y) y
  meet_great : {x y w : T} -> le w x ∧ le w y -> le w (meet x y)

def Lattice.lt (L : Lattice) (a b : L.T) : Prop := L.le a b ∧ a ≠ b

