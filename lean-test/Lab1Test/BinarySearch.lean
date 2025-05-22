def binarySearch (arr : Array Int) (target : Int) : Int :=
  let rec search (low : Nat) (high : Nat) (fuel : Nat) : Int :=
    if fuel = 0 then
      -1  -- Emergency termination (should never happen with enough fuel)
    else if low > high then
      -1  -- Target not found
    else
      let mid := low + (high - low) / 2
      match arr[mid]? with
      | none => -1  -- Invalid index
      | some val =>
        if val == target then
          mid  -- Target found, return the index as Int
        else if val < target then
          search (mid + 1) high (fuel - 1)  -- Search in right half
        else
          search low (mid - 1) (fuel - 1)  -- Search in left half

  -- Initialize with array size as fuel (log₂(n) iterations needed at most)
  search 0 (if arr.size > 0 then arr.size - 1 else 0) arr.size

def binarySearch_spec_correctness (arr : Array Int) (target : Int) (result : Int) : Prop :=
  (result = -1 ∧ ¬(∃ i : Nat, i < arr.size ∧ arr[i]? = some target)) ∨
  (∃ i : Nat, i = result ∧ i < arr.size ∧ arr[i]? = some target)

-- This spec verifies that the array is sorted in ascending order
def binarySearch_spec_sorted (arr : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < arr.size →
    match arr[i]?, arr[j]? with
    | some vi, some vj => vi ≤ vj
    | _, _ => True

-- Helper function to create arrays from lists (for easier testing)
def arrayFromList (list : List Int) : Array Int :=
  list.toArray

-- Test cases using #guard
#guard binarySearch (arrayFromList [1, 2, 3, 4, 5]) 3 = 2
#guard binarySearch (arrayFromList [1, 2, 3, 4, 5]) 1 = 0
#guard binarySearch (arrayFromList [1, 2, 3, 4, 5]) 5 = 4
#guard binarySearch (arrayFromList [1, 2, 3, 4, 5]) 6 = -1
#guard binarySearch (arrayFromList [1, 3, 5, 7, 9]) 7 = 3
#guard binarySearch (arrayFromList []) 5 = -1

-- For duplicate values, binary search finds one of the occurrences (not necessarily the first one)
-- So let's just check that it finds the value, not which index specifically
#eval "Index found for [1, 1, 1, 1, 1] searching for 1: " ++ toString (binarySearch (arrayFromList [1, 1, 1, 1, 1]) 1)
#guard binarySearch (arrayFromList [1, 1, 1, 1, 1]) 1 >= 0   -- Just verify it found the value somewhere

-- Additional test for debugging
#eval "Result of binarySearch [1, 2, 3, 4, 5] 3: " ++ toString (binarySearch (arrayFromList [1, 2, 3, 4, 5]) 3)
