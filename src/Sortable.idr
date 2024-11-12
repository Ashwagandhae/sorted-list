module Sortable
import Decidable.Equality
import Util

public export
record SortableAxiomsNoId (gte : (a -> a -> Bool)) where
  constructor MkSortableAxiomsNoId
  reflexivity : (x : a) -> (x `gte` x = True)
  antisymmetry : (x, y : a) -> (x `gte` y = True) -> (y `gte` x = True) -> (x = y)
  transitivity : (x, y, z : a) -> (x `gte` y = True) -> (y `gte` z = True) -> (x `gte` z = True)
  totality : (x, y : a) -> Either (x `gte` y = True) (y `gte` x = True)
  decEq : (x, y : a) -> Dec (x = y)

public export
record SortableAxioms (gte : (a -> a -> Bool)) where
  constructor MkSortableAxioms

  id : a
  identity : (x : a) -> (x `gte` id = True)

  reflexivity : (x : a) -> (x `gte` x = True)
  antisymmetry : (x, y : a) -> (x `gte` y = True) -> (y `gte` x = True) -> (x = y)
  transitivity : (x, y, z : a) -> (x `gte` y = True) -> (y `gte` z = True) -> (x `gte` z = True)
  totality : (x, y : a) -> Either (x `gte` y = True) (y `gte` x = True)
  decEq : (x, y : a) -> Dec (x = y)

public export
mkMaybeGte : (a -> a -> Bool) -> (Maybe a -> Maybe a -> Bool)
mkMaybeGte gte = res where
  res : (Maybe a -> Maybe a -> Bool)
  res (Just x) (Just y) = gte x y
  res (Just x) Nothing = True
  res Nothing (Just y) = False
  res Nothing Nothing = True

maybeGteReflects : {gte : (a -> a -> Bool)} -> {x, y : a} -> (gte x y = (mkMaybeGte gte) (Just x) (Just y))
maybeGteReflects {gte} {x} {y} = Refl

public export
createIdentityAxioms : {gte : (a -> a -> Bool)} -> SortableAxiomsNoId (gte) -> SortableAxioms (mkMaybeGte gte)
createIdentityAxioms (MkSortableAxiomsNoId reflexivity antisymmetry transitivity totality decEq) =
  MkSortableAxioms Nothing identity reflexivity' antisymmetry' transitivity' totality' decEq' where
    mgte : (Maybe a -> Maybe a -> Bool)
    mgte = mkMaybeGte gte

    identity : (x : Maybe a) -> ((x `mgte` Nothing) = True)
    identity (Just x) = Refl
    identity Nothing = Refl

    reflexivity' : (x : Maybe a) -> (x `mgte` x = True)
    reflexivity' (Just x) = rewrite reflexivity x in Refl
    reflexivity' Nothing = Refl

    antisymmetry' : (x, y : Maybe a) -> (x `mgte` y = True) -> (y `mgte` x = True) -> (x = y)
    antisymmetry' Nothing Nothing xyGte yxGte = Refl
    antisymmetry' (Just x) (Just y) xyGte yxGte =
      let xyGte : (x `gte` y = True) = trans (maybeGteReflects {gte}) xyGte
          yxGte : (y `gte` x = True) = trans (maybeGteReflects {gte}) yxGte
      in cong Just $ antisymmetry x y xyGte yxGte

    transitivity' : (x, y, z : Maybe a) -> (x `mgte` y = True) -> (y `mgte` z = True) -> (x `mgte` z = True)
    transitivity' Nothing Nothing Nothing _ _ = Refl
    transitivity' (Just x) Nothing Nothing _ _ = Refl
    transitivity' (Just x) (Just y) Nothing _ _ = Refl
    transitivity' (Just x) (Just y) (Just z) xyGte yzGte =
      let xyGte = trans (maybeGteReflects {gte}) xyGte
          yzGte = trans (maybeGteReflects {gte}) yzGte
          xzGte = transitivity x y z xyGte yzGte
      in trans (maybeGteReflects {gte}) xzGte

    totality' : (x, y : Maybe a) -> Either (x `mgte` y = True) (y `mgte` x = True)
    totality' Nothing Nothing = Left Refl
    totality' (Just x) Nothing = Left Refl
    totality' Nothing (Just y) = Right Refl
    totality' (Just x) (Just y) = case totality x y of
      Left xyGte => Left $ trans (maybeGteReflects {gte}) xyGte
      Right yxGte => Right $ trans (maybeGteReflects {gte}) yxGte

    DecEq a where
      decEq = decEq

    decEq' : (x, y : Maybe a) -> Dec (x = y)
    decEq' x y = Decidable.Equality.decEq x y

public export
data Sortable: (a : Type) -> Type where
  Sor : (gte : (a -> a -> Bool)) -> SortableAxioms gte -> Sortable a

export
(.gte) : Sortable a -> (a -> a -> Bool)
(.gte) (Sor gte _) = gte

export
(.axioms) : (sor : Sortable a) -> SortableAxioms sor.gte
(.axioms) (Sor _ axioms) = axioms

public export
mkSortable :
  {a : Type}
  -> (gte : (a -> a -> Bool))
  -> (reflexivity : (x : a) -> (x `gte` x = True))
  -> (antisymmetry : (x, y : a) -> (x `gte` y = True) -> (y `gte` x = True) -> (x = y))
  -> (transitivity : (x, y, z : a) -> (x `gte` y = True) -> (y `gte` z = True) -> (x `gte` z = True))
  -> (totality : (x, y : a) -> Either (x `gte` y = True) (y `gte` x = True))
  -> (decEq : (x, y : a) -> Dec (x = y))
  -> Sortable (Maybe a)
mkSortable gte refl antisym trans tot decEq =
  Sor (mkMaybeGte gte) $ createIdentityAxioms (MkSortableAxiomsNoId refl antisym trans tot decEq)

parameters {sor : Sortable a}
  gte : (a -> a -> Bool)
  gte = sor.gte

  export
  sortableEq : a -> a -> Bool
  sortableEq x y = sor.gte x y && sor.gte y x

  export
  notReflexivityImpliesReverse : {sor: Sortable a} -> (x, y : a) -> (sor.gte x y = True) -> (Not (x = y)) -> (sor.gte y x = False)
  notReflexivityImpliesReverse {sor} x y gtePrf neqPrf with (decEq (sor.gte y x) True)
    notReflexivityImpliesReverse {sor} x y gtePrf neqPrf | (Yes prf) = absurd $ neqPrf $ sor.axioms.antisymmetry x y gtePrf prf
    notReflexivityImpliesReverse {sor} x y gtePrf neqPrf | (No prf) = notTrueIsFalse prf

  export
  reflexivityEq : (x, y : a) -> (x = y) -> (sor.gte x y = True)
  reflexivityEq x y prf = p1 y prf where
    p1 : (z : a) -> (x = z) -> (sor.gte x z = True)
    p1 z prf = rewrite prf in sor.axioms.reflexivity z


  export
  max : a -> a -> a
  max x y = if sor.gte x y then x else y

  export
  maxGteTrue : {x, y : a} -> (sor.gte x y = True) -> (max x y = x)
  maxGteTrue {x} {y} prf = rewrite prf in Refl

  export
  maxGteFalse : {x, y : a} -> (sor.gte x y = False) -> (max x y = y)
  maxGteFalse {x} {y} prf = rewrite prf in Refl

  export
  maxId : (x : a) -> (max x sor.axioms.id = x)
  maxId x = maxGteTrue (sor.axioms.identity x)

  export
  maxCommutative : (l, r : a) -> (max l r = max r l)
  maxCommutative l r with ((decEq (l `gte` r) True, decEq (r `gte` l) True))
    maxCommutative l r | (Yes lrTrue, Yes rlTrue) =
      let lrEq : (l = r) = sor.axioms.antisymmetry l r lrTrue rlTrue
        in rewrite lrEq in Refl
    maxCommutative l r | (Yes lrTrue, No rlFalse) =
        let rlFalse : (r `gte` l = False) = notTrueIsFalse rlFalse
            left : (max l r = l) = maxGteTrue lrTrue
            right : (max r l = l) = maxGteFalse rlFalse
        in rewrite right in left
    maxCommutative l r | (No lrFalse, Yes rlTrue) =
        let lrFalse : (l `gte` r = False) = notTrueIsFalse lrFalse
            left : (max r l = r) = maxGteTrue rlTrue
            right : (max l r = r) = maxGteFalse lrFalse
        in rewrite left in right
    maxCommutative l r | (No lrFalse, No rlFalse) =
      case sor.axioms.totality l r of
        Left lrTrue => absurd (lrFalse lrTrue)
        Right rlTrue => absurd (rlFalse rlTrue)

  export
  flipMax : {x, y, z : a} -> (max x y = z) -> (max y x = z)
  flipMax {x} {y} {z} prf = trans (sym (maxCommutative x y)) prf


  export
  maxTotality : (x, y : a) -> Either (max x y = x) (max x y = y)
  maxTotality x y with (decEq (sor.gte x y) True, decEq (sor.gte y x) True)
    maxTotality x y | (Yes xyGte, _) = Left $ maxGteTrue xyGte
    maxTotality x y | (_, Yes yxGte) = Right $ rewrite maxCommutative x y in maxGteTrue yxGte
    maxTotality x y | (No xyGteFalse, No yxGteFalse) =
      case sor.axioms.totality x y of
        Left xyGte => absurd $ xyGteFalse xyGte
        Right yxGte => absurd $ yxGteFalse yxGte

  export
  maxImpliesGte : {x, y : a} -> (max x y = x) -> (sor.gte x y = True)
  maxImpliesGte {x} {y} prf with (decEq (sor.gte x y) True)
    maxImpliesGte {x} {y} prf | (Yes xyGte) = xyGte
    maxImpliesGte {x} {y} prf | (No xyGteFalse) = case sor.axioms.decEq x y of
      Yes xyEq => absurd $ xyGteFalse $ reflexivityEq x y xyEq
      No xyNeq =>
        let prf1 : (max x y = y) = maxGteFalse $ notTrueIsFalse xyGteFalse
            xyEq : (x = y) = rewrite sym prf in prf1
        in absurd $ xyNeq xyEq