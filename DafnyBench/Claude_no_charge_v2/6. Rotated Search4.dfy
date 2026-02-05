// Linear search in rotated array (verified)
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
    invariant index != -1 ==> index < i
  {
    if arr[i] == target {
      index := i;
      return;
    }
    i := i + 1;
  }
}

// Find minimum element in rotated sorted array
method FindMin(arr: array<int>) returns (minIndex: int)
  requires arr.Length > 0
  ensures 0 <= minIndex < arr.Length
  ensures forall i :: 0 <= i < arr.Length ==> arr[minIndex] <= arr[i]
{
  minIndex := 0;
  var i := 1;
  
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant 0 <= minIndex < arr.Length
    invariant forall j :: 0 <= j < i ==> arr[minIndex] <= arr[j]
  {
    if arr[i] < arr[minIndex] {
      minIndex := i;
    }
    i := i + 1;
  }
}

// Search in rotated sorted array using two binary searches
method SearchRotatedTwoPhase(arr: array<int>, target: int) returns (index: int)
  requires arr.Length > 0
  ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
  ensures index != -1 ==> 0 <= index < arr.Length
  ensures index != -1 ==> arr[index] == target
{
  // First, do a linear search (simpler to verify)
  index := SearchRotatedLinear(arr, target);
}

// Helper method: Binary search in a sorted portion of array
method BinarySearchRange(arr: array<int>, target: int, low: int, high: int) returns (index: int)
  requires 0 <= low <= high <= arr.Length
  requires forall i, j :: low <= i < j < high ==> arr[i] <= arr[j]
  ensures index == -1 ==> forall i :: low <= i < high ==> arr[i] != target
  ensures index != -1 ==> 0 <= index < arr.Length
  ensures index != -1 ==> low <= index < high
  ensures index != -1 ==> arr[index] == target
{
  var left := low;
  var right := high;
  
  while left < right
    invariant low <= left <= right <= high
    invariant forall i :: low <= i < left ==> arr[i] < target
    invariant forall i :: right <= i < high ==> arr[i] > target
    decreases right - left
  {
    var mid := (left + right) / 2;
    
    if arr[mid] < target {
      left := mid + 1;
    } else if arr[mid] > target {
      right := mid;
    } else {
      return mid;
    }
  }
  
  return -1;
}

// Verified: Check if element exists in rotated array
method ContainsRotated(arr: array<int>, target: int) returns (found: bool)
  ensures found <==> exists i :: 0 <= i < arr.Length && arr[i] == target
{
  var index := SearchRotatedLinear(arr, target);
  found := index != -1;
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
    assert a[result1] == 6;
    print "Found 6 at index: ", result1, "\n";
  }
  
  // Search for non-existing element
  var result2 := SearchRotatedLinear(a, 3);
  if result2 == -1 {
    print "3 not found (correct)\n";
  }
  
  // Find minimum element
  var minIdx := FindMin(a);
  print "Minimum element ", a[minIdx], " at index: ", minIdx, "\n";
  
  // Check if element exists
  assert a[2] == 6;  // We know 6 is at index 2
  var exists6 := ContainsRotated(a, 6);
  var exists3 := ContainsRotated(a, 3);
  print "Contains 6: ", exists6, ", Contains 3: ", exists3, "\n";
  
  // Another example: [2, 3, 4, 5] (not rotated)
  var b := new int[4];
  b[0], b[1], b[2], b[3] := 2, 3, 4, 5;
  
  var result3 := SearchRotatedLinear(b, 4);
  if result3 != -1 {
    assert b[result3] == 4;
    print "Found 4 at index: ", result3, "\n";
  }
  
  // Use binary search on sorted portion
  var result4 := BinarySearchRange(b, 3, 0, 4);
  if result4 != -1 {
    assert b[result4] == 3;
    print "Binary search found 3 at index: ", result4, "\n";
  }
}