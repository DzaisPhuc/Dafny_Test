// Predicate to check if an array is sorted
predicate IsSorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

method BinarySearch(a: array<int>, key: int) returns (index: int)
  requires a != null
  requires IsSorted(a)
  // If we return a valid index, that element equals key
  ensures 0 <= index < a.Length ==> a[index] == key
  // COMPLETENESS: If we return -1, key doesn't exist anywhere
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
  // Strong postcondition: index is either valid or -1 (no other values)
  ensures index == -1 || (0 <= index < a.Length)
  // COMPLETENESS (other direction): If key exists, we MUST return a valid index
  ensures (exists k :: 0 <= k < a.Length && a[k] == key) ==> (0 <= index < a.Length && a[index] == key)
{
  var low := 0;
  var high := a.Length - 1;
  
  while low <= high
    invariant 0 <= low <= a.Length
    invariant -1 <= high < a.Length
    // CRITICAL: All elements to the left of low are strictly smaller than key
    invariant forall i :: 0 <= i < low ==> a[i] < key
    // CRITICAL: All elements to the right of high are strictly larger than key
    invariant forall i :: high < i < a.Length ==> a[i] > key
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    
    if a[mid] == key {
      return mid;
    } else if a[mid] < key {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  
  return -1;
}

// Test method with a sorted array
method TestBinarySearch()
{
  var arr := new int[7];
  arr[0], arr[1], arr[2], arr[3], arr[4], arr[5], arr[6] := 1, 3, 5, 7, 9, 11, 13;
  
  // Test finding existing elements - verify properties, not specific indices
  var idx1 := BinarySearch(arr, 7);
  assert 0 <= idx1 < arr.Length;
  assert arr[idx1] == 7;
  
  var idx2 := BinarySearch(arr, 1);
  assert 0 <= idx2 < arr.Length;
  assert arr[idx2] == 1;
  
  var idx3 := BinarySearch(arr, 13);
  assert 0 <= idx3 < arr.Length;
  assert arr[idx3] == 13;
  
  // Test finding non-existing elements
  var idx4 := BinarySearch(arr, 8);
  assert idx4 == -1;
  
  var idx5 := BinarySearch(arr, 0);
  assert idx5 == -1;
  
  var idx6 := BinarySearch(arr, 15);
  assert idx6 == -1;
}

// Test with single element
method TestBinarySearchSingle()
{
  var arr := new int[1];
  arr[0] := 42;
  
  var idx1 := BinarySearch(arr, 42);
  assert 0 <= idx1 < arr.Length;
  assert arr[idx1] == 42;
  
  var idx2 := BinarySearch(arr, 10);
  assert idx2 == -1;
}

// Test with empty array
method TestBinarySearchEmpty()
{
  var arr := new int[0];
  
  var idx := BinarySearch(arr, 5);
  assert idx == -1;
}

// Test with duplicates
method TestBinarySearchDuplicates()
{
  var arr := new int[5];
  arr[0], arr[1], arr[2], arr[3], arr[4] := 2, 2, 2, 2, 2;
  
  var idx := BinarySearch(arr, 2);
  // Don't care which index, just that it's valid and contains the key
  assert 0 <= idx < arr.Length;
  assert arr[idx] == 2;
}