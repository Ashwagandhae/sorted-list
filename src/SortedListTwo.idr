-- module SortedListTwo
-- import Sortable
-- import Decidable.Equality
-- import Decidable.Decidable
-- import Delete
-- import Util


-- public export
-- data SortedList : {a : Type} -> (sor : Sortable a) -> (val : Maybe a) -> Type where
--   SNil : SortedList sor Nothing
--   SCons: (g : a) -> (gs : SortedList sor val) -> (mkMaybeGte (sor.gte) (Just g) val = True) -> SortedList sor (Just g)

-- export
-- Cast (SortedList {a} sor val) (List a) where
--   cast SNil = Nil
--   cast (SCons g gs _) = g::(cast gs)

-- parameters {sor : SortableAxiomsNoId a}


--   gte : (a -> a -> Bool)
--   gte = sor.gte

--   id : a
--   id = sor.axioms.id

--   reflexivity : (x : a) -> (x `gte` x = True)
--   reflexivity = sor.axioms.reflexivity

--   antisymmetry : (x, y : a) -> (x `gte` y = True) -> (y `gte` x = True) -> (x = y)
--   antisymmetry = sor.axioms.antisymmetry

--   transitivity : (x, y, z : a) -> (x `gte` y = True) -> (y `gte` z = True) -> (x `gte` z = True)
--   transitivity = sor.axioms.transitivity

--   totality : (x, y : a) -> Either (x `gte` y = True) (y `gte` x = True)
--   totality = sor.axioms.totality

--   -- identity : (x : Maybe a) -> (x `mgte` Nothing = True)
--   -- identity x = Refl

--   -- export
--   -- maybeCons : {val : _} -> (x : a) -> SortedList sor val -> Maybe (SortedList sor x)
--   -- maybeCons {val} x xs with (decEq (x `gte` val) True)
--   --   maybeCons {val} x xs | Yes prf = Just $ SCons x xs prf
--   --   maybeCons {val} x xs | No _ = Nothing

--   export
--   getHead : List a -> a
--   getHead [] = id
--   getHead (x :: _) = x

--   -- export
--   -- maybeSortedList : (xs : List a) -> Maybe (SortedList sor (getHead xs))
--   -- maybeSortedList [] = Just SNil
--   -- maybeSortedList (x :: xs) = (maybeSortedList xs) >>= (maybeCons x)

--   export
--   listMax : List a -> a
--   listMax [] = sor.axioms.id
--   listMax (x::xs) = max {sor} x (listMax xs)

--   listMaxNil : (listMax [] = sor.axioms.id)
--   listMaxNil = Refl

--   listMaxCons : (listMax (x::xs) = max {sor} x (listMax xs))
--   listMaxCons = Refl

--   -- export
--   -- sortedToList : SortedList sor v -> List a
--   -- sortedToList SNil = []
--   -- sortedToList (SCons x xs _) = x::(sortedToList xs)

--   deleteFirstPredicate : a -> (Bool, a -> Bool -> (Bool, Bool))
--   deleteFirstPredicate target = (False, del) where
--     del : a -> Bool -> (Bool, Bool)
--     del elem done = if done
--       then (True, True)
--       else if sortableEq {sor} elem target
--         then (False, True)
--         else (True, False)

--   lmax : List a -> a
--   lmax = listMax
--   parameters (s : state, p : a -> state -> (Bool, state))
--     del : List a -> List a
--     del = deleteBy s p

--     listMaxGteDeleteByListMax : (xs : List a) -> (gte (listMax xs) (lmax (del xs)) = True)
--     listMaxGteDeleteByListMax [] =
--       let res : (sor.axioms.id `gte` sor.axioms.id = True) = rewrite identity id in Refl
--           res : ((listMax []) `gte` sor.axioms.id = True) = rewrite listMaxNil in res

--           idEqListMaxNil : (xs : List a) -> (xs = []) -> (sor.axioms.id = lmax xs)
--           idEqListMaxNil xs prf = rewrite prf in listMaxNil

--           nilEqDeleteBy : (xs : List a) -> (xs = []) -> (del xs = [])
--           nilEqDeleteBy xs prf = rewrite prf in deleteByNil s p

--           idEqListMaxDeleteByNil : (xs : List a) -> (xs = []) -> (sor.axioms.id = lmax (del xs))
--           idEqListMaxDeleteByNil xs prf =
--             let lem : (del xs = []) = nilEqDeleteBy xs prf
--                 res : (sor.axioms.id = (lmax (del xs))) = idEqListMaxNil (del xs) lem
--             in res

--           res : (gte (listMax []) (lmax (del [])) = True)
--           res = rewrite idEqListMaxDeleteByNil [] Refl in res
--       in res
--     listMaxGteDeleteByListMax (x::xs) with (decPEq s p x)
--       listMaxGteDeleteByListMax (x::xs) | (newS ** (Left prf)) =
--         let
--           delxs : List a
--           delxs = (deleteBy newS p xs)
--         in
--         case (maxTotality x (lmax xs), maxTotality {sor} x (lmax delxs)) of
--           (Left xGte, Left xGteDel) =>
--             let res : (x = x) = Refl
--                 res : ((max x (lmax xs)) = max x (lmax delxs)) = trans xGte (sym xGteDel)
--                 res : ((max x (lmax xs)) `gte` (max x (lmax delxs)) = True) =
--                   reflexivityEq {sor} (max x (lmax xs)) (max x (lmax delxs)) res
--             in rewrite prf in res
--           (Right xsGte, Right xsDelGte) =>
--             -- p1: lm xs >= x
--             -- p2: lm del xs >= x
--             -- rec: lm xs >= lm del xs
--             -- wts : max x (lm xs) >= max x (lm del xs)
--             -- given p1 and p2, we can rewrite rec
--             -- rec -> max x (lm xs) >= max x (lm del xs), qed
--             let rec : ((lmax xs) `gte` (lmax delxs) = True) = listMaxGteDeleteByListMax newS p xs
--                 res : ((max x (lmax xs)) `gte` (lmax delxs) = True) =
--                   replace {p = (\k => gte k (lmax delxs) = True)} (sym xsGte) rec
--                 res : ((max x (lmax xs)) `gte` (max x (lmax delxs)) = True) =
--                   replace {p = (\k => ((max {sor} x (lmax xs)) `gte` k) = True)} (sym xsDelGte) res
--             in rewrite prf in res
--           (Left xGte, Right xsDelGte) =>
--             -- p1: x >= lm xs
--             -- p2: lm del xs >= x
--             -- rec: lm xs >= lm del xs
--             -- wts : max x (lm xs) >= max x (lm del xs)
--             -- by trans p1 p2, p3: lm del xs >= lm xs
--             -- by antisymmetry: lm del xs = lm xs
--             let rec : ((lmax xs) `gte` (lmax delxs) = True) = listMaxGteDeleteByListMax newS p xs
--                 p1 : (x `gte` (lmax xs) = True) = maxImpliesGte xGte
--                 p2 : ((lmax delxs) `gte` x = True) = maxImpliesGte $ flipMax xsDelGte
--                 p3 : ((lmax delxs) `gte` (lmax xs) = True) =
--                   transitivity (lmax delxs) x (lmax xs) p2 p1
--                 p4 : (lmax xs = lmax delxs) = sym $
--                   antisymmetry (lmax delxs) (lmax xs) p3 rec
--                 res : ((max x (lmax xs)) `gte` (max x (lmax delxs)) = True) =
--                   replace {p=(\k => ((max {sor} x (lmax xs)) `gte` (max {sor} x k) = True))} p4 $ reflexivity (max {sor} x (lmax xs))
--             in rewrite prf in res
--           (Right xsGte, Left xGteDel) =>
--             -- p1: lm xs >= x
--             -- p2: x >= lm del xs
--             -- rec: lm xs >= lm del xs
--             -- wts: max x (lm xs) >= max x (lm del xs)
--             -- rw wts with p1 p2: lm xs >= x
--             let rec : ((lmax xs) `gte` (lmax delxs) = True) = listMaxGteDeleteByListMax newS p xs
--                 rightGteSide : (lmax xs = max x (lmax xs)) = sym xsGte
--                 leftGteSide : (x = max x (lmax delxs)) = sym xGteDel
--                 res : ((lmax xs) `gte` x = True) = maxImpliesGte $ flipMax xsGte
--                 res : ((max x (lmax xs)) `gte` x = True) =
--                   replace {p=(\k => (k `gte` x = True))} rightGteSide res
--                 res : ((max x (lmax xs)) `gte` (max x (lmax delxs)) = True) =
--                   replace {p=(\k => ((max {sor} x (lmax xs)) `gte` k = True))} leftGteSide res
--             in rewrite prf in res
--       listMaxGteDeleteByListMax (x::xs) | (newS ** Right prf) =
--         let
--             delxs : List a
--             delxs = (deleteBy newS p xs)
--         in
--         case (maxTotality x (lmax xs)) of
--           (Left xMax) =>
--           -- we know that x > lm xs
--           -- we know that lm xs > lm del xs
--           -- by transitive property we know that x > lm del xs
--             let xMax : (max x (lmax xs) = x) = xMax
--                 xGte : (x `gte` (lmax xs) = True) = maxImpliesGte {sor} xMax
--                 rec : ((lmax xs) `gte` (lmax delxs) = True) = listMaxGteDeleteByListMax newS p xs
--                 res : (x `gte` (lmax delxs) = True) =
--                   transitivity x (lmax xs) (lmax delxs) xGte rec
--                 res : ((max x (lmax xs)) `gte` (lmax delxs) = True) =
--                   replace {p = (\k => (k `gte` (lmax delxs) = True))} (sym xMax) res
--             in rewrite prf in res
--           (Right xsMax) =>
--             let xsMax : (max x (lmax xs) = (lmax xs)) = xsMax
--                 rec : ((lmax xs) `gte` (lmax delxs) = True) = listMaxGteDeleteByListMax newS p xs
--                 res : ((max x (lmax xs)) `gte` (lmax delxs) = True) =
--                   replace {p = (\k => (k `gte` (lmax delxs) = True))} (sym xsMax) rec
--             in rewrite prf in res





--   export
--   selectionSort : (xs : List a) -> (SortedList sor (listMax xs))
--   selectionSort [] = SNil
--   selectionSort xs =
--     let (s, p) = deleteFirstPredicate (listMax xs)
--         prf: ((listMax xs) `gte` (listMax (deleteBy s p xs)) = True) =
--           listMaxGteDeleteByListMax s p xs
--     in SCons (listMax xs) (selectionSort (deleteBy s p xs)) prf

