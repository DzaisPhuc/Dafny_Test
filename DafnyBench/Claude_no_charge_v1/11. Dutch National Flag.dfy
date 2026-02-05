// Predicate: All elements are 0, 1, or 2
predicate IsValid(a: array<int>)
  reads a
{
  forall i :: 0 <= i < a.Length ==> a[i] in {0, 1, 2}
}

// Predicate: Array is sorted
predicate IsSorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

method Sort3Colors(a: array<int>)
  requires IsValid(a)
  modifies a
  ensures IsSorted(a)
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures IsValid(a)
{
  if a.Length <= 1 {
    return;
  }
  
  var low := 0;    // Boundary: [0..low) contains 0s
  var mid := 0;    // Boundary: [low..mid) contains 1s
  var high := a.Length - 1;  // Boundary: (high..Length) contains 2s
  
  ghost var originalArray := a[..];
  
  while mid <= high
    invariant 0 <= low <= mid <= high + 1 <= a.Length
    invariant IsValid(a)
    invariant multiset(a[..]) == multiset(originalArray)
    // Region [0..low) contains only 0s
    invariant forall i :: 0 <= i < low ==> a[i] == 0
    // Region [low..mid) contains only 1s
    invariant forall i :: low <= i < mid ==> a[i] == 1
    // Region (high..Length) contains only 2s
    invariant forall i :: high < i < a.Length ==> a[i] == 2
    decreases high - mid
  {
    if a[mid] == 0 {
      // Swap a[low] and a[mid], move both pointers forward
      a[low], a[mid] := a[mid], a[low];
      low := low + 1;
      mid := mid + 1;
    } else if a[mid] == 1 {
      // Already in correct position, just move mid forward
      mid := mid + 1;
    } else {
      // a[mid] == 2
      // Swap a[mid] and a[high], move high backward
      // Don't move mid because we haven't examined the swapped element yet
      a[mid], a[high] := a[high], a[mid];
      high := high - 1;
    }
  }
  
  // After loop: [0..low) has 0s, [low..mid) has 1s, [mid..Length) has 2s
  // Since mid > high, we have mid == high + 1, so the array is fully partitioned
}

// Helper lemma: Multiset equality is preserved after swap
lemma SwapPreservesMultiset(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  ensures multiset(a[..]) == multiset(old(a[..]))
  modifies a
{
  a[i], a[j] := a[j], a[i];
}

// Test method with various cases
method TestSort3Colors() {
  // Test 1: Standard case
  var a1 := new int[6] [2, 0, 2, 1, 1, 0];
  Sort3Colors(a1);
  assert a1[0] == 0 && a1[1] == 0;
  assert a1[2] == 1 && a1[3] == 1;
  assert a1[4] == 2 && a1[5] == 2;
  assert IsSorted(a1);
  
  // Test 2: Already sorted
  var a2 := new int[5] [0, 0, 1, 2, 2];
  Sort3Colors(a2);
  assert IsSorted(a2);
  
  // Test 3: Reverse sorted
  var a3 := new int[6] [2, 2, 1, 1, 0, 0];
  Sort3Colors(a3);
  assert IsSorted(a3);
  
  // Test 4: All same elements
  var a4 := new int[4] [1, 1, 1, 1];
  Sort3Colors(a4);
  assert IsSorted(a4);
  
  // Test 5: Single element
  var a5 := new int[1] [2];
  Sort3Colors(a5);
  assert IsSorted(a5);
  
  // Test 6: Two elements
  var a6 := new int[2] [2, 0];
  Sort3Colors(a6);
  assert a6[0] == 0 && a6[1] == 2;
  assert IsSorted(a6);
  
  // Test 7: Only 0s and 2s
  var a7 := new int[4] [2, 0, 2, 0];
  Sort3Colors(a7);
  assert IsSorted(a7);
}

// Method to verify the three-region property visually
method PrintArray(a: array<int>)
  requires IsValid(a)
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
  {
    // In actual use, this would print the array
    i := i + 1;
  }
}

// Advanced test: Verify permutation property explicitly
method TestPermutationProperty() {
  var a := new int[7] [2, 0, 1, 2, 0, 1, 2];
  ghost var before := multiset(a[..]);
  
  Sort3Colors(a);
  
  ghost var after := multiset(a[..]);
  assert before == after;
  assert IsSorted(a);
}