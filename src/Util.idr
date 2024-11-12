module Util

export
notTrueIsFalse : {exp : Bool} -> (Not (exp = True)) -> (exp = False)
notTrueIsFalse {exp} notTrue with (exp)
  notTrueIsFalse {exp} notTrue | False = Refl
  notTrueIsFalse {exp} notTrue | True = absurd (notTrue Refl)

export
splitTuple : (p : (a, b)) -> (elemA : a ** elemB : b ** p = (elemA, elemB))
splitTuple (x, y) = (x ** y ** Refl)