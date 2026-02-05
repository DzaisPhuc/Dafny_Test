// Binary search in a sorted array
method BinarySearch(arr: array<int>, target: int) returns (index: int)
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
  ensures index != -1 ==> 0 <= index < arr.Length
  ensures index != -1 ==> arr[index] == target
{
  var left := 0;
  var right := arr.Length;
  
  while left < right
    invariant 0 <= left <= right <= arr.Length
    invariant forall i :: 0 <= i < left ==> arr[i] < target
    invariant forall i :: right <= i < arr.Length ==> arr[i] > target
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

// Binary search that returns the leftmost occurrence
method BinarySearchLeftmost(arr: array<int>, target: int) returns (index: int)
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
  ensures index != -1 ==> 0 <= index < arr.Length
  ensures index != -1 ==> arr[index] == target
  ensures index != -1 ==> forall i :: 0 <= i < index ==> arr[i] < target
{
  var left := 0;
  var right := arr.Length;
  
  while left < right
    invariant 0 <= left <= right <= arr.Length
    invariant forall i :: 0 <= i < left ==> arr[i] < target
    invariant forall i :: right <= i < arr.Length ==> arr[i] >= target
    decreases right - left
  {
    var mid := (left + right) / 2;
    
    if arr[mid] < target {
      left := mid + 1;
    } else {
      right := mid;
    }
  }
  
  if left < arr.Length && arr[left] == target {
    return left;
  }
  return -1;
}

// Binary search that returns the rightmost occurrence
method BinarySearchRightmost(arr: array<int>, target: int) returns (index: int)
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures index == -1 ==> forall i :: 0 <= i < arr.Length ==> arr[i] != target
  ensures index != -1 ==> 0 <= index < arr.Length
  ensures index != -1 ==> arr[index] == target
  ensures index != -1 ==> forall i :: index < i < arr.Length ==> arr[i] > target
{
  var left := 0;
  var right := arr.Length;
  
  while left < right
    invariant 0 <= left <= right <= arr.Length
    invariant forall i :: 0 <= i < left ==> arr[i] <= target
    invariant forall i :: right <= i < arr.Length ==> arr[i] > target
    decreases right - left
  {
    var mid := (left + right) / 2;
    
    if arr[mid] <= target {
      left := mid + 1;
    } else {
      right := mid;
    }
  }
  
  if left > 0 && arr[left - 1] == target {
    return left - 1;
  }
  return -1;
}

// Find the lower bound (first position where arr[i] >= target)
method LowerBound(arr: array<int>, target: int) returns (index: int)
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures 0 <= index <= arr.Length
  ensures forall i :: 0 <= i < index ==> arr[i] < target
  ensures forall i :: index <= i < arr.Length ==> arr[i] >= target
{
  var left := 0;
  var right := arr.Length;
  
  while left < right
    invariant 0 <= left <= right <= arr.Length
    invariant forall i :: 0 <= i < left ==> arr[i] < target
    invariant forall i :: right <= i < arr.Length ==> arr[i] >= target
    decreases right - left
  {
    var mid := (left + right) / 2;
    
    if arr[mid] < target {
      left := mid + 1;
    } else {
      right := mid;
    }
  }
  
  return left;
}

// Find the upper bound (first position where arr[i] > target)
method UpperBound(arr: array<int>, target: int) returns (index: int)
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures 0 <= index <= arr.Length
  ensures forall i :: 0 <= i < index ==> arr[i] <= target
  ensures forall i :: index <= i < arr.Length ==> arr[i] > target
{
  var left := 0;
  var right := arr.Length;
  
  while left < right
    invariant 0 <= left <= right <= arr.Length
    invariant forall i :: 0 <= i < left ==> arr[i] <= target
    invariant forall i :: right <= i < arr.Length ==> arr[i] > target
    decreases right - left
  {
    var mid := (left + right) / 2;
    
    if arr[mid] <= target {
      left := mid + 1;
    } else {
      right := mid;
    }
  }
  
  return left;
}

// Count occurrences of target in sorted array
method CountOccurrences(arr: array<int>, target: int) returns (count: int)
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures count >= 0
  ensures count <= arr.Length
{
  if arr.Length == 0 {
    count := 0;
    return;
  }
  
  var lower := LowerBound(arr, target);
  var upper := UpperBound(arr, target);
  
  // From the postconditions, we know:
  // lower: forall i :: 0 <= i < lower ==> arr[i] < target
  // upper: forall i :: 0 <= i < upper ==> arr[i] <= target
  // Since arr[i] < target implies arr[i] <= target, we have lower <= upper
  
  count := upper - lower;
}

// Check if element exists (optimized version)
method Contains(arr: array<int>, target: int) returns (found: bool)
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures found <==> exists i :: 0 <= i < arr.Length && arr[i] == target
{
  var index := BinarySearch(arr, target);
  found := index != -1;
}

// Test method
method Main()
{
  // Sorted array: [1, 3, 5, 7, 9, 11, 13]
  var a := new int[7];
  a[0], a[1], a[2] := 1, 3, 5;
  a[3], a[4], a[5], a[6] := 7, 9, 11, 13;
  
  // Basic binary search
  var result1 := BinarySearch(a, 7);
  if result1 != -1 {
    print "Found 7 at index: ", result1, "\n";
  }
  
  var result2 := BinarySearch(a, 6);
  if result2 == -1 {
    print "6 not found (correct)\n";
  }
  
  // Test with duplicates: [1, 2, 2, 2, 3, 4, 5]
  var b := new int[7];
  b[0], b[1], b[2], b[3] := 1, 2, 2, 2;
  b[4], b[5], b[6] := 3, 4, 5;
  
  var leftmost := BinarySearchLeftmost(b, 2);
  var rightmost := BinarySearchRightmost(b, 2);
  print "Leftmost 2 at index: ", leftmost, "\n";
  print "Rightmost 2 at index: ", rightmost, "\n";
  
  // Lower and upper bounds
  var lower := LowerBound(b, 2);
  var upper := UpperBound(b, 2);
  print "Lower bound of 2: ", lower, "\n";
  print "Upper bound of 2: ", upper, "\n";
  
  // Count occurrences
  var count := CountOccurrences(b, 2);
  print "Count of 2: ", count, "\n";
  
  // Contains check
  var has2 := Contains(b, 2);
  var has6 := Contains(b, 6);
  print "Contains 2: ", has2, ", Contains 6: ", has6, "\n";
  
  // Edge cases
  var c := new int[1];
  c[0] := 5;
  var single := BinarySearch(c, 5);
  print "Single element search: ", single, "\n";
  
  var empty := new int[0];
  var emptyResult := BinarySearch(empty, 1);
  print "Empty array search: ", emptyResult, "\n";
}