# idris2 sorted list

## what is it?

My first realish project with idris2. It contains data types for lists that are guaranteed to be sorted, and a selectionSort implementation that converts a list into a sorted list.

In order to sort a `List a`, you must construct a `Sortable a` with an ordering function `gte` that satisfies ordering axioms:

1. reflexivity : (x : a) -> (x `gte` x = True)
2. antisymmetry : (x, y : a) -> (x `gte` y = True) -> (y `gte` x = True) -> (x = y)
3. transitivity : (x, y, z : a) -> (x `gte` y = True) -> (y `gte` z = True) -> (x `gte` z = True)
4. totality : (x, y : a) -> Either (x `gte` y = True) (y `gte` x = True)

The type `a` must also implement `DecEq`.

Currently, there is also another pair of axioms required: `id : a`, and `identity : (x : a) -> (x `gte` id)`. These are primarily there to give empty lists a maximum value. In the future, I will just automatically turn a `Sortable a` with the four axioms into `Sortable (Maybe a)` with six axioms where `Nothing` is the identity.

In the variable naming for the implementation and the explanation below, it's assumed that `gte` actually tells you if x is _greater than_ or equal to y to make it easier for me to think about, which also means that SortedList is descending by default. But you can still have a ascendingly sorted list by supplying a <= function instead of a >= function—it will satsify all the axioms.

```haskell
data Sortable: (a : Type) -> Type where
  Sor : (gte : (a -> a -> Bool)) -> SortableAxioms gte -> Sortable a
```

Then you can call `SortedList.selectionSort` on the list, and it will give you a `SortedList` with this structure, which is guaranteed to order its elements in _descending_ order.

`SortedList` looks like this:

```haskell
data SortedList : {a : Type} -> (sor : Sortable a) -> (val : a) -> Type where
  SNil : SortedList sor sor.axioms.id
  SCons: (g : a) -> (gs : SortedList sor val) -> ((sor.gte) g val = True) -> SortedList sor g
```

It's basically the same structure as a normal list, but each Cons is indexed by the value it contains, which happens to be the maximum of the list because it is a sorted list. Constructing Cons also requires a proof that the value of the head is >= the maximum of the tail, which guarantees that the list remains sorted. Nil is then just indexed by some id value that's guaranteed to be <= than any other element of type `a`; for example, for the natural numbers, this value id is 0.

## notes

### skill issue

I don't know how to use idris! There are probably many ways to implement this better.

### why no sortable interface?

I didn't make a sortable interface because that would require each type to only have one ordering. However, sometimes it makes sense for a type to have multiple orderings. For example, a type `(Nat, Nat)` could be ordered with the following functions:

```haskell
gteFirst : (Nat, Nat) -> (Nat, Nat) -> Bool
gteFirst (x, _) (y, _) = gte x y

gteSecond : (Nat, Nat) -> (Nat, Nat) -> Bool
gteSecond (_, x) (_, y) = gte x y
```

Additionally, I didn't have to write different code for ascending and descending ordering, because those two are just considered distinct orderings.

### fake type safety

Currently, `SortedList.selectionSort` is not actually typesafe because its only guaranteed to return a `SortedList sor (listMax {sor} xs)` for a list xs. Thus, an evil selectionSort implementer could write the function like this:

```haskell
selectionSortEvil : {sor : Sortable a} -> (xs : List a) -> (SortedList sor (listMax {sor} xs))
selectionSortEvil {sor} xs = SCons (listMax xs) SNil $ sor.axioms.identity (listMax xs)
```

I will try to ensure that the output is a reordering of the input in future versions.
