def mergeSort (arr : Array Int) : Array Int :=
  -- Helper function to merge two sorted arrays
  let merge (left : Array Int) (right : Array Int) : Array Int :=
    let rec loop (i j : Nat) (result : Array Int) (fuel : Nat) : Array Int :=
      if fuel = 0 then
        result -- Emergency exit (should never happen with enough fuel)
      else if i >= left.size && j >= right.size then
        result -- Both arrays are fully processed
      else if i >= left.size then
        -- Left array is exhausted, add the rest of right array
        loop i (j + 1) (result.push right[j]!) (fuel - 1)
      else if j >= right.size then
        -- Right array is exhausted, add the rest of left array
        loop (i + 1) j (result.push left[i]!) (fuel - 1)
      else if left[i]! <= right[j]! then
        -- Take element from left array
        loop (i + 1) j (result.push left[i]!) (fuel - 1)
      else
        -- Take element from right array
        loop i (j + 1) (result.push right[j]!) (fuel - 1)

    loop 0 0 #[] (left.size + right.size + 1)

  -- Main merge sort recursive function
  let rec sort (input : Array Int) (fuel : Nat) : Array Int :=
    if fuel = 0 then
      input -- Emergency exit (should never happen with enough fuel)
    else if input.size <= 1 then
      input -- Base case: already sorted
    else
      let mid := input.size / 2

      -- Create and fill left half
      let leftHalf := (Array.mk [] : Array Int).append (input.extract 0 mid)

      -- Create and fill right half
      let rightHalf := (Array.mk [] : Array Int).append (input.extract mid input.size)

      -- Recursively sort both halves
      let sortedLeft := sort leftHalf (fuel - 1)
      let sortedRight := sort rightHalf (fuel - 1)

      -- Merge the sorted halves
      merge sortedLeft sortedRight

  -- Start the sorting with enough fuel (2n should be more than enough)
  sort arr (2 * arr.size)

-- This spec verifies that the output is sorted in ascending order
def mergeSort_spec_sorted (_arr : Array Int) (result : Array Int) : Prop :=
  ∀ i j : Nat, i < j → j < result.size → result[i]! ≤ result[j]!

-- This spec verifies that the output is a permutation of the input
def mergeSort_spec_permutation (arr : Array Int) (result : Array Int) : Prop :=
  arr.size = result.size ∧
  ∀ value : Int,
    (arr.toList.count value) = (result.toList.count value)

-- Helper function to create arrays from lists (for easier testing)
def arrayFromList (list : List Int) : Array Int :=
  list.toArray

-- Helper function to check if an array is sorted
def isSorted (arr : Array Int) : Bool :=
  let rec check (i : Nat) (fuel : Nat) : Bool :=
    if fuel = 0 then
      true -- Emergency exit (should never happen with enough fuel)
    else if i + 1 >= arr.size then
      true -- End of array - it's sorted
    else if arr[i]! > arr[i+1]! then
      false -- Found unsorted elements
    else
      check (i + 1) (fuel - 1) -- Continue checking

  check 0 arr.size

-- Test cases
#guard isSorted (mergeSort (arrayFromList [5, 3, 1, 4, 2]))
#guard mergeSort (arrayFromList [5, 3, 1, 4, 2]) = arrayFromList [1, 2, 3, 4, 5]
#guard mergeSort (arrayFromList [1, 2, 3, 4, 5]) = arrayFromList [1, 2, 3, 4, 5]
#guard mergeSort (arrayFromList [5, 4, 3, 2, 1]) = arrayFromList [1, 2, 3, 4, 5]
#guard mergeSort (arrayFromList []) = arrayFromList []
#guard mergeSort (arrayFromList [3, 3, 3, 3]) = arrayFromList [3, 3, 3, 3]
#guard mergeSort (arrayFromList [-5, 10, -3, 8, 0, -1]) = arrayFromList [-5, -3, -1, 0, 8, 10]

-- Additional test for visualization
#eval "Original: [5, 3, 1, 4, 2], Sorted: " ++ toString (mergeSort (arrayFromList [5, 3, 1, 4, 2]))
