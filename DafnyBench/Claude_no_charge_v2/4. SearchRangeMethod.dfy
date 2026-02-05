method SearchInRange(arr: array<int>, target: int, low: int, high: int) returns (index: int)
  requires 0 <= low <= high <= arr.Length
  ensures index == -1 ==> forall i :: low <= i < high ==> arr[i] != target
  ensures 0 <= index < arr.Length ==> low <= index < high && arr[index] == target
{
  index := -1;
  var i := low;
  
  while i < high
    invariant low <= i <= high
    invariant index == -1 ==> forall j :: low <= j < i ==> arr[j] != target
    invariant 0 <= index < arr.Length ==> low <= index < i && arr[index] == target
  {
    if arr[i] == target {
      index := i;
      return;
    }
    i := i + 1;
  }
}

// Example with sorted array for binary search in range
method BinarySearchInRange(arr: array<int>, target: int, low: int, high: int) returns (index: int)
  requires 0 <= low <= high <= arr.Length
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures index == -1 ==> forall i :: low <= i < high ==> arr[i] != target
  ensures 0 <= index < arr.Length ==> low <= index < high && arr[index] == target
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

// Test method demonstrating usage
method Main()
{
  var a := new int[10];
  a[0], a[1], a[2], a[3], a[4] := 5, 10, 15, 20, 25;
  a[5], a[6], a[7], a[8], a[9] := 30, 35, 40, 45, 50;
  
  // Search for 20 in range [2, 7)
  var result := SearchInRange(a, 20, 2, 7);
  assert result == 3;
  
  // Binary search for 35 in range [0, 10)
  var result2 := BinarySearchInRange(a, 35, 0, 10);
  assert result2 == 6;
  
  print "Linear search found 20 at index: ", result, "\n";
  print "Binary search found 35 at index: ", result2, "\n";
}