// Binary search with full Dafny verification
// Searches for a target value in a sorted array

predicate sorted(a: array<int>, low: int, high: int)
  reads a
  requires 0 <= low <= high <= a.Length
{
  forall i, j :: low <= i < j < high ==> a[i] <= a[j]
}

method BinarySearch(a: array<int>, target: int) returns (index: int)
  requires sorted(a, 0, a.Length)
  ensures 0 <= index < a.Length ==> a[index] == target
  ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != target
{
  var low := 0;
  var high := a.Length;
  
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant sorted(a, 0, a.Length)
    invariant forall i :: 0 <= i < low ==> a[i] < target
    invariant forall i :: high <= i < a.Length ==> a[i] > target
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    
    if a[mid] < target {
      low := mid + 1;
    } else if a[mid] > target {
      high := mid;
    } else {
      return mid;
    }
  }
  
  return -1;
}

// Example usage with test method
method Main()
{
  var arr := new int[7];
  arr[0], arr[1], arr[2], arr[3], arr[4], arr[5], arr[6] := 1, 3, 5, 7, 9, 11, 13;
  
  // Explicitly prove the array is sorted by asserting pairwise comparisons
  assert arr[0] <= arr[1] <= arr[2] <= arr[3] <= arr[4] <= arr[5] <= arr[6];
  assert forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j];
  
  var idx := BinarySearch(arr, 7);
  print "Found 7 at index ", idx, "\n";
  
  idx := BinarySearch(arr, 4);
  print "Searching for 4: ", idx, "\n";
}