module Delete
import Decidable.Equality
import Util


public export
deleteBy : (s : state) -> (p : a -> state -> (Bool, state)) -> List a -> List a
deleteBy _ _ [] = []
deleteBy s p (x :: xs) =
  let (add, newS) = p x s
      rec = deleteBy newS p xs
  in if add then x::rec else rec

public export
deleteByNil : (s : state) -> (p : a -> state -> (Bool, state)) -> (deleteBy s p [] = [])
deleteByNil s p = Refl

public export
deleteByConsTrue : (s : state) -> (p : a -> state -> (Bool, state)) ->
  (x : a) -> (xs : List a) -> (newS : state) -> (p x s = (True, newS)) ->
  (deleteBy s p (x::xs) = x :: (deleteBy newS p xs))
deleteByConsTrue s p x xs newS prf = rewrite prf in Refl

public export
deleteByConsFalse : (s : state) -> (p : a -> state -> (Bool, state)) ->
  (x : a) -> (xs : List a) -> (newS : state) -> (p x s = (False, newS)) ->
  (deleteBy s p (x::xs) = deleteBy newS p xs)
deleteByConsFalse s p x xs newS prf = rewrite prf in Refl

export
decPEqComputed : (s : state) -> (p : a -> state -> (Bool, state)) -> (x : a) -> (add : Bool) -> (newS : state) -> (p x s = (add, newS)) -> Either (p x s = (True, newS)) (p x s = (False, newS))
decPEqComputed s p x add newS res with (decEq add True)
  decPEqComputed s p x add newS res | Yes prf = Left $ rewrite sym prf in res
  decPEqComputed s p x add newS res | No prf = Right $ rewrite sym (notTrueIsFalse prf) in res

export
decPEq : (s : state) -> (p : a -> state -> (Bool, state)) -> (x : a) -> (newS **  Either (p x s = (True, newS)) (p x s = (False, newS)))
decPEq s p x =
    let (add ** newS ** prf) = splitTuple {a=Bool} {b=state} (p x s)
    in (newS ** decPEqComputed {a} {state} s p x add newS prf)