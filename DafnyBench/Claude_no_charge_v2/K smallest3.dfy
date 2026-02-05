// Simple selection sort approach to find k smallest
  i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant forall j :: 0 <= j < i ==> result[j] == temp[j]
    invariant forall j :: 0 <= j < i ==> 
      forall m :: j < m < temp.Length ==> temp[j] <= temp[m]
    invariant forall j :: 0 <= j < i ==> 
      exists m :: 0 <= m < arr.Length && result[j] == arr[m]
  {
    // Find minimum in remaining elements
    var minIdx := i;
    var j := i + 1;
    
    while j < temp.Length
      invariant i <= minIdx < temp.Length
      invariant i + 1 <= j <=// Find the K smallest elements in an array (returns them in a new array)
method FindKSmallest(arr: array<int>, k: int) returns (result: array<int>)
  requires 0 <= k <= arr.Length
  ensures result.Length == k
  ensures forall i :: 0 <= i < result.Length ==> 
    exists j :: 0 <= j < arr.Length && result[i] == arr[j]
{
  result := new int[k];
  
  if k == 0 {
    return;
  }
  
  // Copy all elements to work with
  var temp := new int[arr.Length];
  var i := 0;
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> temp[j] == arr[j]
  {
    temp[i] := arr[i];
    i := i + 1;
  }
  
  assert forall j :: 0 <= j < arr.Length ==> temp[j] == arr[j];
  
  // Simple selection sort approach to find k smallest
  i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant forall j :: 0 <= j < i ==> result[j] == temp[j]
    invariant forall j :: 0 <= j < i ==> 
      forall m :: j < m < temp.Length ==> temp[j] <= temp[m]
    invariant forall j :: 0 <= j < temp.Length ==> 
      exists m :: 0 <= m < arr.Length && temp[j] == arr[m]
  {
    // Find minimum in remaining elements
    var minIdx := i;
    var j := i + 1;
    
    while j < temp.Length
      invariant i <= minIdx < temp.Length
      invariant i + 1 <= j <= temp.Length
      invariant forall m :: i <= m < j ==> temp[minIdx] <= temp[m]
    {
      if temp[j] < temp[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    
    // Swap
    var t := temp[i];
    temp[i] := temp[minIdx];
    temp[minIdx] := t;
    
    result[i] := temp[i];
    i := i + 1;
  }
}

// Find the Kth smallest element (1-indexed, so k=1 is the minimum)
method FindKthSmallest(arr: array<int>, k: int) returns (value: int)
  requires arr.Length > 0
  requires 1 <= k <= arr.Length
  ensures exists i :: 0 <= i < arr.Length && arr[i] == value
{
  var temp := new int[arr.Length];
  var i := 0;
  
  // Copy array
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant forall j :: 0 <= j < i ==> temp[j] == arr[j]
  {
    temp[i] := arr[i];
    i := i + 1;
  }
  
  assert forall j :: 0 <= j < arr.Length ==> temp[j] == arr[j];
  
  // Selection sort to find kth smallest
  i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant forall j :: 0 <= j < i ==> 
      forall m :: j < m < temp.Length ==> temp[j] <= temp[m]
    invariant forall j :: 0 <= j < temp.Length ==> 
      exists m :: 0 <= m < arr.Length && temp[j] == arr[m]
  {
    var minIdx := i;
    var j := i + 1;
    
    while j < temp.Length
      invariant i <= minIdx < temp.Length
      invariant i + 1 <= j <= temp.Length
      invariant forall m :: i <= m < j ==> temp[minIdx] <= temp[m]
    {
      if temp[j] < temp[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    
    var t := temp[i];
    temp[i] := temp[minIdx];
    temp[minIdx] := t;
    
    i := i + 1;
  }
  
  value := temp[k - 1];
}

// Find minimum element (special case: 1st smallest)
method FindMin(arr: array<int>) returns (minValue: int)
  requires arr.Length > 0
  ensures exists i :: 0 <= i < arr.Length && arr[i] == minValue
  ensures forall i :: 0 <= i < arr.Length ==> minValue <= arr[i]
{
  minValue := arr[0];
  var i := 1;
  
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant exists j :: 0 <= j < arr.Length && arr[j] == minValue
    invariant forall j :: 0 <= j < i ==> minValue <= arr[j]
  {
    if arr[i] < minValue {
      minValue := arr[i];
    }
    i := i + 1;
  }
}

// Find maximum element
method FindMax(arr: array<int>) returns (maxValue: int)
  requires arr.Length > 0
  ensures exists i :: 0 <= i < arr.Length && arr[i] == maxValue
  ensures forall i :: 0 <= i < arr.Length ==> maxValue >= arr[i]
{
  maxValue := arr[0];
  var i := 1;
  
  while i < arr.Length
    invariant 1 <= i <= arr.Length
    invariant exists j :: 0 <= j < arr.Length && arr[j] == maxValue
    invariant forall j :: 0 <= j < i ==> maxValue >= arr[j]
  {
    if arr[i] > maxValue {
      maxValue := arr[i];
    }
    i := i + 1;
  }
}

// Count how many elements are less than or equal to a value
method CountLessOrEqual(arr: array<int>, value: int) returns (count: int)
  ensures 0 <= count <= arr.Length
  ensures count == |set i | 0 <= i < arr.Length && arr[i] <= value|
{
  count := 0;
  var i := 0;
  
  while i < arr.Length
    invariant 0 <= i <= arr.Length
    invariant count == |set j | 0 <= j < i && arr[j] <= value|
  {
    if arr[i] <= value {
      count := count + 1;
    }
    i := i + 1;
  }
}

// Test method
method Main()
{
  // Test array: [7, 10, 4, 3, 20, 15]
  var a := new int[6];
  a[0], a[1], a[2] := 7, 10, 4;
  a[3], a[4], a[5] := 3, 20, 15;
  
  // Find 3 smallest elements
  var k3 := FindKSmallest(a, 3);
  print "3 smallest elements: ";
  var i := 0;
  while i < k3.Length
    invariant 0 <= i <= k3.Length
  {
    print k3[i], " ";
    i := i + 1;
  }
  print "\n";
  
  // Find the 2nd smallest element
  var kth2 := FindKthSmallest(a, 2);
  print "2nd smallest element: ", kth2, "\n";
  
  // Find minimum
  var min := FindMin(a);
  print "Minimum element: ", min, "\n";
  
  // Find maximum
  var max := FindMax(a);
  print "Maximum element: ", max, "\n";
  
  // Test with smaller array
  var b := new int[4];
  b[0], b[1], b[2], b[3] := 5, 2, 8, 1;
  
  var k2 := FindKSmallest(b, 2);
  print "2 smallest from [5,2,8,1]: ";
  i := 0;
  while i < k2.Length
    invariant 0 <= i <= k2.Length
  {
    print k2[i], " ";
    i := i + 1;
  }
  print "\n";
  
  // Find 1st smallest (minimum)
  var kth1 := FindKthSmallest(b, 1);
  print "1st smallest (min): ", kth1, "\n";
  
  // Count elements <= 5
  var cnt := CountLessOrEqual(b, 5);
  print "Count of elements <= 5: ", cnt, "\n";
}