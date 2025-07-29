import Latticefiability.System
import Latticefiability.Lattice

structure LatticeFor (S : System) where
  lat : Lattice
  map : S.El -> lat.T
  le : {a b : S.El} -> S.le a b -> lat.le (map a) (map b)
  lt : {a b : S.El} -> S.lt a b -> lat.lt (map a) (map b)
  join : {j x y : S.El} -> S.join j x y -> map j = lat.join (map x) (map y)
  meet : {m x y : S.El} -> S.meet m x y -> map m = lat.meet (map x) (map y)

