import Latticefiability.System

structure Complete (S : System) : Prop where
  le_refl : {a : S.El} -> S.le a a
  le_le : {a b c : S.El} -> S.le a b -> S.le b c -> S.le a c
  lt_imp_le : {a b : S.El} -> S.lt a b -> S.le a b
  le_lt : {a b c : S.El} -> S.le a b -> S.lt b c -> S.lt a c
  lt_le : {a b c : S.El} -> S.lt a b -> S.le b c -> S.lt a c
  join_upper : {j x y : S.El} -> S.join j x y -> And (S.le x j) (S.le y j)
  join_least : {j x y b : S.El} -> S.join j x y -> S.le x b -> S.le y b -> S.le j b
  meet_lower : {m x y : S.El} -> S.meet m x y -> And (S.le m x) (S.le m y)
  meet_great : {m x y b : S.El} -> S.meet m x y -> S.le b x -> S.le b y -> S.le b m
  lt_irrefl : {a : S.El} -> Not (S.lt a a)

namespace Complete

  theorem eq_refl (C : Complete S) {a : S.El} : S.eq a a := And.intro C.le_refl C.le_refl

  theorem eq_symm (_ : Complete S) {a b : S.El} : S.eq a b -> S.eq b a := And.symm

  theorem eq_eq (C : Complete S) {a b c : S.El} (h1 : S.eq a b) (h2 : S.eq b c) : S.eq a c :=
    And.intro (C.le_le h1.left h2.left) (C.le_le h2.right h1.right)

  theorem le_eq (C : Complete S) {a b c : S.El} (h1 : S.le a b) (h2 : S.eq b c) : S.le a c :=
    C.le_le (h1) (h2.left)

  theorem eq_le (C : Complete S) {a b c : S.El} (h1 : S.eq a b) (h2 : S.le b c) : S.le a c :=
    C.le_le (h1.left) (h2)

  theorem lt_eq (C : Complete S) {a b c : S.El} (h1 : S.lt a b) (h2 : S.eq b c) : S.lt a c :=
    C.lt_le h1 h2.left

  theorem eq_lt (C : Complete S) {a b c : S.El} (h1 : S.eq a b) (h2 : S.lt b c) : S.lt a c :=
    C.le_lt h1.left h2

  theorem lt_lt (C : Complete S) (a b c : S.El) (h1 : S.lt a b) (h2 : S.lt b c) : S.lt a c :=
    C.lt_le h1 (C.lt_imp_le h2)

  theorem lt_imp_not_ge (C : Complete S) {a b : S.El} (h1 : S.lt a b) (h2: S.le b a) : False :=
    C.lt_irrefl (C.lt_le h1 h2)

  theorem dual (C : Complete S) : Complete S.dual := {
    le_refl := C.le_refl
    le_le := fun a b => C.le_le b a
    lt_imp_le := C.lt_imp_le
    le_lt := fun a b => C.lt_le b a
    lt_le := fun a b => C.le_lt b a
    join_upper := C.meet_lower
    join_least := C.meet_great
    meet_lower := C.join_upper
    meet_great := C.join_least
    lt_irrefl := C.lt_irrefl
  }

end Complete

structure Completed (S : System) where
  S' : System
  C : Complete S'
  el : S.El = S'.El
  le : {a b : S.El} -> S.le a b -> S'.le (cast el a) (cast el b)
  lt : {a b : S.El} -> S.lt a b -> S'.lt (cast el a) (cast el b)
  join : {j x y : S.El} -> S.join j x y -> S'.join (cast el j) (cast el x) (cast el y)
  meet : {m x y : S.El} -> S.meet m x y -> S'.meet (cast el m) (cast el x) (cast el y)

