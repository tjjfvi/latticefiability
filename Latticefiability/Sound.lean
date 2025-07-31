import Latticefiability.System
import Latticefiability.Complete
import Latticefiability.Lattice
import Latticefiability.LatticeFor

structure LatEl (S : System) where
  has : S.El -> Prop
  complete : {a b : S.El} -> S.le a b -> has b -> has a
  join : {j x y : S.El} -> S.join j x y -> has x -> has y -> has j

def lat_el_eq {S : System} {a b : LatEl S} (h : (e : S.El) -> a.has e ↔ b.has e) : a = b := by
  have : a.has = b.has := by funext; rw [eq_iff_iff]; apply_assumption
  cases a; cases b; simp_all

inductive Join (S : System) (a b : S.El -> Prop) : (e : S.El) -> Prop where
  | inl : a e -> Join S a b e
  | inr : b e -> Join S a b e
  | join : {j x y : S.El} -> Join S a b x -> Join S a b y -> S.join j x y -> S.le e j -> Join S a b e

def complete_to_lattice_for {S : System} (C : Complete S) : LatticeFor S := {
  lat := {
    T := LatEl S

    le := fun a b => (e : S.El) -> a.has e -> b.has e

    join := fun a b => {
      has := fun e => Join S a.has b.has e
      complete := by
        intro _ _ _ j
        cases j
        . apply Join.inl; apply a.complete <;> assumption
        . apply Join.inr; apply b.complete <;> assumption
        . rename_i ha hb hj _; apply Join.join ha hb hj; apply C.le_le <;> assumption
      join := by intro _ _ _ hj jx jy; apply Join.join jx jy hj C.le_refl
    }

    meet := fun a b => {
      has := fun e => a.has e ∧ b.has e
      complete := by (repeat intro h); cases h; apply And.intro <;> apply LatEl.complete <;> assumption
      join := by intro _ _ _ _ x y; cases x; cases y; apply And.intro <;> apply LatEl.join <;> assumption
    }

    refl := by (repeat intro); assumption
    trans := by (repeat intro); simp [*]
    antisymm := by (repeat intro); apply lat_el_eq; intro; apply Iff.intro <;> apply_assumption

    meet_lower := by (repeat intro); apply And.intro <;> (repeat intro) <;> simp [*]
    meet_great := by (repeat intro); simp [*]

    join_upper := by (repeat intro); apply And.intro <;> intro _ h; exact Join.inl h; exact Join.inr h
    join_least := by
      intro _ _ w h _ j
      induction j
      . simp_all
      . simp_all
      . apply w.complete; assumption
        cases h
        apply w.join <;> apply_assumption
  }

  map := fun e => {
    has := fun f => S.le f e
    complete := C.le_le
    join := C.join_least
  }

  le := fun h1 => by intro _ h2; exact C.le_le h2 h1

  lt := fun {a b} h1 => by
    apply And.intro
    . intro _ h2
      exact C.le_le h2 (C.lt_imp_le h1)
    . intro h2
      apply C.lt_imp_not_ge h1
      replace h2 := congrArg (fun x => x.has b) h2
      simp at h2
      rw [h2]
      exact C.le_refl

  meet := fun hm => by
    apply lat_el_eq; intro
    apply Iff.intro
    . intro h
      apply And.intro <;> apply C.le_le (by assumption)
      . exact (C.meet_lower hm).left
      . exact (C.meet_lower hm).right
    . intro h
      apply C.meet_great hm <;> simp_all

  join := fun hj => by
    apply lat_el_eq; intro
    apply Iff.intro
    . intro h
      exact Join.join (Join.inl C.le_refl) (Join.inr C.le_refl) hj h
    . intro h
      simp_all
      induction h <;> apply C.le_le (by assumption)
      . exact (C.join_upper hj).left
      . exact (C.join_upper hj).right
      . apply C.join_least <;> assumption
}

def completed_to_lattice_for {S : System} (C : Completed S) : LatticeFor S :=
  let base := complete_to_lattice_for C.C
  {
    lat := base.lat
    map := fun x => base.map (cast C.el x)
    le := fun l => base.le (C.le l)
    lt := fun l => base.lt (C.lt l)
    join := fun j => base.join (C.join j)
    meet := fun m => base.meet (C.meet m)
  }

def lattice_for_to_completed {S : System} (L : LatticeFor S) : Completed S := {
  S' := {
    El := S.El
    le := fun a b => L.lat.le (L.map a) (L.map b)
    lt := fun a b => L.lat.lt (L.map a) (L.map b)
    join := S.join
    meet := S.meet
  }
  C := {
    le_refl := L.lat.refl
    le_le := L.lat.trans
    lt_imp_le := And.left

    le_lt := by
      intro _ _ _ h1 h2
      apply And.intro
      . exact L.lat.trans h1 h2.left
      . simp_all
        intro h
        rw [h] at h1
        apply h2.right
        exact L.lat.antisymm h2.left h1

    lt_le := by
      intro _ _ _ h1 h2
      apply And.intro
      . exact L.lat.trans h1.left h2
      . simp_all
        intro h
        rw [h] at h1
        apply h1.right
        exact L.lat.antisymm h1.left h2

    join_upper := by
      intro _ _ _ h
      simp; rw [L.join h]
      exact L.lat.join_upper

    join_least := by
      intro _ _ _ _ hj hx hy
      simp; rw [L.join hj]
      exact L.lat.join_least (And.intro hx hy)

    meet_lower := by
      intro _ _ _ h
      simp; rw [L.meet h]
      exact L.lat.meet_lower

    meet_great := by
      intro _ _ _ _ hm hx hy
      simp; rw [L.meet hm]
      exact L.lat.meet_great (And.intro hx hy)

    lt_irrefl := by
      intro _ h
      apply h.right
      rfl
  }
  el := rfl
  le := L.le
  lt := L.lt
  join := id
  meet := id
}
