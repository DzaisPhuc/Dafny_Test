// Helper predicate to check if array is rotated sorted
predicate IsRotatedSorted(arr: array<int>)
  reads arr
{
  arr.Length == 0 ||
  exists pivot :: 0 <= pivot < arr.Length &&
    (forall i, j :: 0 <= i < j < pivot ==> arr[i] <= arr[j]) &&
    (forall i, j :: pivot <= i < j < arr.Length ==> arr[i] <= arr[j]) &&
    (pivot == 0 || arr[pivot - 1] > arr[pivot]) &&
    (pivot == 0 || arr[arr.Length - 1] < arr[0])
}

// Linear search in rotated array (simpler verification)
method SearchRotatedLinear(arr: array<int>, target: int) returns (index: int)
  ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
  ensures index != -1 ==> 0 <= index < arr.Length
  ensures index != -1 ==> arr[index] == target
{
  index := -1;
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant index == -1 ==> forall j :: 0 <= j < i ==> arr[j] != target
    invariant index != -1 ==> 0 <= index < arr.Length
    invariant index != -1 ==> arr[index] == target
  {
    if arr[i] == target {
      index := i;
      return;
    }
    i := i + 1;
  }
}

// Binary search in rotated sorted array
method SearchRotatedBinary(arr: array<int>, target: int) returns (index: int)
  requires arr.Length > 0
  requires IsRotatedSorted(arr)
  ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
  ensures index != -1 ==> 0 <= index < arr.Length
  ensures index != -1 ==> arr[index] == target
{
  var left := 0;
  var right := arr.Length;
  
  while left < right
    invariant 0 <= left <= right <= arr.Length
    decreases right - left
  {
    var mid := (left + right) / 2;
    
    if arr[mid] == target {
      return mid;
    }
    
    // Determine which half is sorted
    if arr[left] <= arr[mid] {
      // Left half is sorted
      if arr[left] <= target < arr[mid] {
        right := mid;
      } else {
        left := mid + 1;
      }
    } else {
      // Right half is sorted
      if arr[mid] < target <= arr[right - 1] {
        left := mid + 1;
      } else {
        right := mid;
      }
    }
  }
  
  return -1;
}

// Find the pivot (rotation point) in a rotated sorted array
method FindPivot(arr: array<int>) returns (pivot: int)
  requires arr.Length > 0
  requires IsRotatedSorted(arr)
  ensures 0 <= pivot < arr.Length
  ensures forall i :: 0 <= i < pivot ==> (i + 1 < arr.Length ==> arr[i] <= arr[i + 1])
  ensures pivot > 0 ==> arr[pivot - 1] > arr[pivot]
{
  if arr.Length == 1 {
    return 0;
  }
  
  var left := 0;
  var right := arr.Length - 1;
  
  // If array is not rotated
  if arr[left] <= arr[right] {
    return 0;
  }
  
  while left < right
    invariant 0 <= left <= right < arr.Length
    decreases right - left
  {
    var mid := (left + right) / 2;
    
    if mid + 1 < arr.Length && arr[mid] > arr[mid + 1] {
      return mid + 1;
    }
    
    if arr[mid] < arr[left] {
      right := mid;
    } else {
      left := mid + 1;
    }
  }
  
  return left;
}

// Test method
method Main()
{
  // Rotated sorted array: [4, 5, 6, 7, 0, 1, 2]
  var a := new int[7];
  a[0], a[1], a[2], a[3] := 4, 5, 6, 7;
  a[4], a[5], a[6] := 0, 1, 2;
  
  // Search for existing element
  var result1 := SearchRotatedLinear(a, 6);
  if result1 != -1 {
    assert arr[result1] == 6;
    print "Found 6 at index: ", result1, "\n";
  }
  
  // Search for non-existing element
  var result2 := SearchRotatedLinear(a, 3);
  assert result2 == -1;
  print "Searching for 3 (not found): ", result2, "\n";
  
  // Another example: [2, 3, 4, 5]
  var b := new int[4];
  b[0], b[1], b[2], b[3] := 2, 3, 4, 5;
  
  var result3 := SearchRotatedLinear(b, 4);
  if result3 != -1 {
    assert b[result3] == 4;
    print "Found 4 at index: ", result3, "\n";
  }
}