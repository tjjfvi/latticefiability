
structure System where
  El : Type
  le : El -> El -> Prop
  lt : El -> El -> Prop
  join : El -> El -> El -> Prop
  meet : El -> El -> El -> Prop

def System.eq (S : System) (a b : S.El) : Prop := S.le a b ∧ S.le b a

def System.dual (S : System) : System := {
  El := S.El
  le := fun a b => S.le b a
  lt := fun a b => S.lt b a
  join := S.meet
  meet := S.join
}
