module Main
import NatSortable
import Sortable
import SortedList

showMaybeList : String -> Maybe (List Nat) -> IO ()
showMaybeList name m = putStrLn $ name ++ ": " ++ case m of
  Just xs => show xs
  Nothing => "no list"

main : IO ()
main = do
  let original : List Nat = [1, 5, 2, 3, 4, 27, 1, 8]
  printLn original


  let sor = natGteSor
  let sorted = selectionSort {sor} $ map Just original
  printLn $ sortedToList (sorted)