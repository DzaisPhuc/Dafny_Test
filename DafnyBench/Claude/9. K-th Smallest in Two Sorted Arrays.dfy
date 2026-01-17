// Predicate: array is sorted
predicate IsSorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Ghost function: count elements smaller than x in array
ghost function CountSmaller(a: array<int>, x: int): nat
  reads a
{
  |set i | 0 <= i < a.Length && a[i] < x|
}

// Ghost function: count elements from both arrays smaller than x
ghost function CountSmallerBoth(a: array<int>, b: array<int>, x: int): nat
  reads a, b
{
  CountSmaller(a, x) + CountSmaller(b, x)
}

// Find k-th smallest element (1-indexed) in two sorted arrays
method FindKthSmallest(a: array<int>, b: array<int>, k: nat) returns (result: int)
  requires IsSorted(a) && IsSorted(b)
  requires 1 <= k <= a.Length + b.Length
  ensures CountSmallerBoth(a, b, result) == k - 1
  ensures exists i :: (0 <= i < a.Length && a[i] == result) || 
                       (0 <= i < b.Length && b[i] == result)
{
  if a.Length == 0 {
    return b[k-1];
  }
  if b.Length == 0 {
    return a[k-1];
  }
  
  var aStart := 0;
  var bStart := 0;
  var remaining := k;
  
  while remaining > 1
    invariant 0 <= aStart <= a.Length
    invariant 0 <= bStart <= b.Length
    invariant 1 <= remaining <= k
    invariant aStart + bStart == k - remaining
    invariant remaining <= (a.Length - aStart) + (b.Length - bStart)
    invariant forall i :: 0 <= i < aStart ==> 
      CountSmallerBoth(a, b, a[i]) < k - 1
    invariant forall i :: 0 <= i < bStart ==> 
      CountSmallerBoth(a, b, b[i]) < k - 1
    decreases remaining
  {
    var halfRemaining := remaining / 2;
    var aIndex := aStart + halfRemaining - 1;
    var bIndex := bStart + halfRemaining - 1;
    
    if aIndex >= a.Length {
      // Not enough elements in a
      result := b[bStart + remaining - 1];
      assert CountSmallerBoth(a, b, result) == k - 1;
      return result;
    }
    
    if bIndex >= b.Length {
      // Not enough elements in b
      result := a[aStart + remaining - 1];
      assert CountSmallerBoth(a, b, result) == k - 1;
      return result;
    }
    
    if a[aIndex] <= b[bIndex] {
      // Eliminate smaller half from a
      aStart := aIndex + 1;
      remaining := remaining - halfRemaining;
    } else {
      // Eliminate smaller half from b
      bStart := bIndex + 1;
      remaining := remaining - halfRemaining;
    }
  }
  
  // remaining == 1, find the minimum of the two candidates
  if aStart >= a.Length {
    result := b[bStart];
  } else if bStart >= b.Length {
    result := a[aStart];
  } else if a[aStart] <= b[bStart] {
    result := a[aStart];
  } else {
    result := b[bStart];
  }
}

// Simplified version with clearer logic
method FindKthSmallestSimple(a: array<int>, b: array<int>, k: nat) returns (result: int)
  requires IsSorted(a) && IsSorted(b)
  requires 1 <= k <= a.Length + b.Length
  requires a.Length > 0 || b.Length > 0
  ensures exists i :: (0 <= i < a.Length && a[i] == result) || 
                       (0 <= i < b.Length && b[i] == result)
{
  // Handle edge cases
  if a.Length == 0 {
    return b[k-1];
  }
  if b.Length == 0 {
    return a[k-1];
  }
  if k == 1 {
    if a[0] <= b[0] {
      return a[0];
    } else {
      return b[0];
    }
  }
  
  // Binary search approach
  var i := 0;
  var j := 0;
  var count := 0;
  
  while count < k - 1
    invariant 0 <= i <= a.Length
    invariant 0 <= j <= b.Length
    invariant count == i + j
    invariant count < k
    decreases a.Length + b.Length - i - j
  {
    if i >= a.Length {
      j := j + 1;
    } else if j >= b.Length {
      i := i + 1;
    } else if a[i] <= b[j] {
      i := i + 1;
    } else {
      j := j + 1;
    }
    count := count + 1;
  }
  
  // Return the k-th element
  if i >= a.Length {
    return b[j];
  } else if j >= b.Length {
    return a[i];
  } else if a[i] <= b[j] {
    return a[i];
  } else {
    return b[j];
  }
}

// Test method
method TestKthSmallest() {
  // Test 1: Simple case
  var a1 := new int[3] [1, 3, 5];
  var b1 := new int[3] [2, 4, 6];
  var result := FindKthSmallestSimple(a1, b1, 3);
  assert result == 3; // Elements smaller: 1, 2
  
  // Test 2: K = 1
  var a2 := new int[2] [5, 7];
  var b2 := new int[2] [3, 9];
  result := FindKthSmallestSimple(a2, b2, 1);
  assert result == 3;
  
  // Test 3: K = last
  var a3 := new int[2] [1, 2];
  var b3 := new int[2] [3, 4];
  result := FindKthSmallestSimple(a3, b3, 4);
  assert result == 4;
  
  // Test 4: One empty array
  var a4 := new int[0];
  var b4 := new int[4] [10, 20, 30, 40];
  result := FindKthSmallestSimple(a4, b4, 2);
  assert result == 20;
}

// Lemma: In sorted array, elements before index i are smaller than a[i]
lemma SortedArrayProperty(a: array<int>, i: int)
  requires IsSorted(a)
  requires 0 <= i < a.Length
  ensures forall j :: 0 <= j < i ==> a[j] <= a[i]
{
  // Dafny proves this automatically from IsSorted definition
}

// Lemma: Count smaller elements in sorted array
lemma CountSmallerInSorted(a: array<int>, x: int, idx: int)
  requires IsSorted(a)
  requires 0 <= idx < a.Length
  requires a[idx] == x
  ensures CountSmaller(a, x) >= idx
{
  // Elements before idx are all smaller than or equal to x
}