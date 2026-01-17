// Predicate: array is rotated sorted (one rotation point or fully sorted)
predicate IsRotatedSorted(a: array<int>)
  reads a
{
  exists k :: 0 <= k <= a.Length &&
    (forall i, j :: 0 <= i < j < k ==> a[i] <= a[j]) &&
    (forall i, j :: k <= i < j < a.Length ==> a[i] <= a[j]) &&
    (k == 0 || k == a.Length || a[k-1] > a[k])
}

// Ghost function: check if target exists in a sequence
ghost predicate ExistsInSeq(s: seq<int>, target: int) {
  exists i :: 0 <= i < |s| && s[i] == target
}

method SearchRotatedArray(a: array<int>, target: int) returns (index: int)
  requires IsRotatedSorted(a)
  ensures index >= 0 ==> 0 <= index < a.Length && a[index] == target
  ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != target
{
  if a.Length == 0 {
    return -1;
  }
  
  var left := 0;
  var right := a.Length - 1;
  
  while left <= right
    invariant 0 <= left <= a.Length
    invariant -1 <= right < a.Length
    invariant left > right ==> forall k :: 0 <= k < a.Length ==> a[k] != target
    invariant forall k :: 0 <= k < left ==> a[k] != target
    invariant forall k :: right < k < a.Length ==> a[k] != target
    decreases right - left
  {
    var mid := left + (right - left) / 2;
    
    if a[mid] == target {
      return mid;
    }
    
    // Determine which half is sorted
    if a[left] <= a[mid] {
      // Left half is sorted
      if a[left] <= target < a[mid] {
        // Target is in sorted left half
        assert forall k :: mid < k <= right ==> a[k] != target;
        right := mid - 1;
      } else {
        // Target is not in sorted left half, must be in right half if exists
        assert forall k :: left <= k <= mid ==> a[k] != target;
        left := mid + 1;
      }
    } else {
      // Right half is sorted (a[mid] < a[left])
      if a[mid] < target <= a[right] {
        // Target is in sorted right half
        assert forall k :: left <= k < mid ==> a[k] != target;
        left := mid + 1;
      } else {
        // Target is not in sorted right half, must be in left half if exists
        assert forall k :: mid <= k <= right ==> a[k] != target;
        right := mid - 1;
      }
    }
  }
  
  return -1;
}

// Helper lemma to establish properties of rotated sorted arrays
lemma RotatedSortedProperties(a: array<int>, left: int, mid: int, right: int)
  requires 0 <= left <= mid <= right < a.Length
  requires IsRotatedSorted(a)
  ensures a[left] <= a[mid] ==> 
    forall i, j :: left <= i < j <= mid ==> a[i] <= a[j]
  ensures a[mid] <= a[right] ==> 
    forall i, j :: mid <= i < j <= right ==> a[i] <= a[j]
{
  // This lemma helps reason about sorted portions
}

// Test method to demonstrate correctness
method TestSearch() {
  var a := new int[7] [4, 5, 6, 7, 0, 1, 2];
  
  var idx := SearchRotatedArray(a, 0);
  assert idx == 4;
  
  idx := SearchRotatedArray(a, 3);
  assert idx == -1;
  
  idx := SearchRotatedArray(a, 4);
  assert idx == 0;
  
  idx := SearchRotatedArray(a, 2);
  assert idx == 6;
}