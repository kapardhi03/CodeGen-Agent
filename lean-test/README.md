# Lab 1 - Test Report

## Implementation Approach

### Binary Search Implementation

For the binary search algorithm, I implemented a **recursive solution** that efficiently searches for a target value in a sorted array. Key aspects of my approach include:

- **Termination Guarantee**: I incorporated a `fuel` parameter to ensure the recursion terminates even in edge cases. This is a common pattern in Lean 4 to satisfy the termination checker.
- **Bounds Handling**: The implementation carefully manages the `low` and `high` bounds, adjusting them based on comparison results with the target value.
- **Index Calculation**: I used the standard binary search optimization for calculating the midpoint:  
  `(low + (high - low) / 2)` to prevent potential integer overflow.
- **Empty Array Handling**: Special handling ensures the function correctly returns `-1` for empty arrays.

### Merge Sort Implementation

For the merge sort algorithm, I implemented a classic **divide-and-conquer** approach with these key features:

- **Efficient Merge Operation**: The `merge` function efficiently combines two sorted arrays while preserving the sorted order.
- **Array Splitting**: I used Lean's `Array.extract` method to divide the input array into two halves.
- **Recursive Sorting**: Each half is recursively sorted before being merged together.
- **Termination Control**: Similar to the binary search implementation, I used a `fuel` parameter to guarantee termination in Lean’s formal context.

---

## Challenges Faced

### Lean 4 Termination Checker

The most significant challenge was satisfying Lean's **termination checker**. Standard recursive algorithms that are obviously terminating to humans require **explicit mechanisms** in Lean to prove termination. I addressed this using a `fuel` parameter that decreases with each recursive call.

### Mutable Variables

Initial attempts to use mutable variables (`let mut`) failed, as the version of Lean didn’t support this syntax. I had to refactor my approach to use **immutable variables** and **functional programming patterns**.

### Array Manipulation

Working with arrays in Lean required learning specific methods like `Array.extract` and understanding the distinction between nullable (`arr[i]?`) and non-nullable (`arr[i]!`) indexing operations.

### Type Conversion Issues

Early attempts faced issues with converting between `Nat` and `Int` types. I had to adjust the implementation to maintain **type consistency** throughout.

---

## Validation Process

I validated my solutions using multiple approaches:

- **Incremental Development**: Built the solutions step by step, testing each component before moving on to the next.
- **Test Cases**: Created comprehensive test cases covering:
  - Standard cases (elements found in the middle, beginning, and end)
  - Edge cases (empty arrays, arrays with a single element)
  - Special cases (arrays with duplicate values)
  - Negative numbers and various array sizes

- **Formal Specifications**: Captured the essential properties:
  - *Binary Search*: Correctness of found indices and handling of not-found cases
  - *Merge Sort*: Ensuring the output is sorted and is a permutation of the input

- **Lean Environment Testing**: Used Lean's `#guard` and `#eval` commands to verify implementations on all test cases.

---

## What I Learned

- **Formal Verification**: Gained practical experience with formal verification in Lean 4, learning how to specify and verify properties of algorithms.
- **Functional Programming**: Deepened understanding of functional programming patterns, especially working with **immutable data structures**.
- **Lean 4 Syntax**: Learned the specific syntax and features of Lean 4, including how to:
  - Work with arrays
  - Define recursive functions
  - Specify algorithmic properties
- **Algorithm Implementation**: Implemented classic algorithms in a **formal verification context**, which requires more rigor than typical programming environments.
- **Termination Proofs**: Learned techniques for **proving algorithm termination**, a fundamental aspect of formal verification.

---

_This report documents my process, challenges, validations, and learnings from Lab 1 of my formal methods course in Lean 4._
