def mergeSort (arr : Array Int) : Array Int :=
  -- << CODE START >>
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
  -- << CODE END >>

def mergeSort_spec_sorted (_arr : Array Int) (result : Array Int) : Prop :=
  -- << SPEC START >>
  ∀ i j : Nat, i < j → j < result.size → result[i]! ≤ result[j]!
  -- << SPEC END >>

def mergeSort_spec_permutation (arr : Array Int) (result : Array Int) : Prop :=
  -- << SPEC START >>
  arr.size = result.size ∧
  ∀ value : Int, 
    (arr.toList.count value) = (result.toList.count value)
  -- << SPEC END >>
