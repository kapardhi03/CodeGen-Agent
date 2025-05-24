def binarySearch (arr : Array Int) (target : Int) : Int :=
  -- << CODE START >>
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
  -- << CODE END >>

def binarySearch_spec_correctness (arr : Array Int) (target : Int) (result : Int) : Prop :=
  -- << SPEC START >>
  (result = -1 ∧ ¬(∃ i : Nat, i < arr.size ∧ arr[i]? = some target)) ∨
  (∃ i : Nat, i = result ∧ i < arr.size ∧ arr[i]? = some target)
  -- << SPEC END >>

def binarySearch_spec_sorted (arr : Array Int) : Prop :=
  -- << SPEC START >>
  ∀ i j : Nat, i < j → j < arr.size →
    match arr[i]?, arr[j]? with
    | some vi, some vj => vi ≤ vj
    | _, _ => True
  -- << SPEC END >>
