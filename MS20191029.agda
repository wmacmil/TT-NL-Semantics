module MS20191029
          -- (t : Set)
          -- (IsTrue : t -> Set)
          (e : Set) where

data Falsity : Set where

t = Set
VP = e -> t
NP = VP -> t  --- (e -> t) -> t
CN = e -> t

properNoun : e -> NP
properNoun x vp = vp x

every : CN -> VP -> t -- uttery useless as a proposition (this useful as a PROGRAM)
every cn vp = (x : e) -> cn x -> vp x

module Example
         (walk : VP)
         (man : CN)
         (JOHN : e)
         (johnMan : man JOHN)
         (p : every man walk)
       where

  john : NP
  john = λ vp → vp JOHN
  -- p' : every man walk
  -- p' x x₁ = {!!}

  johnWalksProof : john walk
  johnWalksProof = {!!} -- p JOHN johnMan
