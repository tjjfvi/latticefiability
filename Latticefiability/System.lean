
structure System where
  El : Type
  le : El -> El -> Prop
  lt : El -> El -> Prop
  join : El -> El -> El -> Prop
  meet : El -> El -> El -> Prop

def System.eq (S : System) (a b : S.El) : Prop := And (S.le a b) (S.le b a)

def System.dual (S : System) : System := System.mk S.El (fun a b => S.le b a) (fun a b => S.lt b a) S.meet S.join
