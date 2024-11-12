
module NatSortable
import Data.Nat
import Sortable
import Decidable.Equality

LTEImpliesGte : (x, y : Nat) -> (LTE x y) -> (y `gte` x = True)
LTEImpliesGte 0 y LTEZero = Refl
LTEImpliesGte (S x) (S y) (LTESucc lte) = LTEImpliesGte x y lte

natReflexivity : (x : Nat) -> (x `gte` x = True)
natReflexivity Z = Refl
natReflexivity (S n) = natReflexivity n

natAntisymmetry : (x, y : Nat) -> (x `gte` y = True) -> (y `gte` x = True) -> (x = y)
natAntisymmetry x y xyGte yxGte =
    let yxLte : (LTE y x) = gteReflectsGTE x y xyGte
        xyLte : (LTE x y) = gteReflectsGTE y x yxGte
    in antisymmetric xyLte yxLte

natTransitivity : (x, y, z : Nat) -> (x `gte` y = True) -> (y `gte` z = True) -> (x `gte` z = True)
natTransitivity x y z xyGte yzGte =
  let yxLte : (LTE y x) = gteReflectsGTE x y xyGte
      zyLte : (LTE z y) = gteReflectsGTE y z yzGte
      zxLte : (LTE z x) = transitive zyLte yxLte
  in LTEImpliesGte z x zxLte

natTotality' : (x, y : Nat) -> Either (LTE x y) (LTE y x)
natTotality' Z Z = Left LTEZero
natTotality' Z (S m) = Left LTEZero
natTotality' (S n) Z = Right LTEZero
natTotality' (S n) (S m) =
  case natTotality' n m of
    Left p => Left (LTESucc p)
    Right p => Right (LTESucc p)

natTotality : (x, y : Nat) -> Either (x `gte` y = True) (y `gte` x = True)
natTotality x y = case natTotality' x y of
  Right prf => Left (LTEImpliesGte y x prf)
  Left prf => Right (LTEImpliesGte x y prf)

natDecEq : (x, y : Nat) -> Dec (x = y)
natDecEq x y = decEq x y

public export
natGteSor : Sortable (Maybe Nat)
natGteSor = mkSortable gte natReflexivity natAntisymmetry natTransitivity natTotality natDecEq