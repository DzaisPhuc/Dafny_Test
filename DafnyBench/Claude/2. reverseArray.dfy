method ReverseArray(a: array<int>)
  requires a != null
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{
  var left := 0;
  var right := a.Length - 1;
  
  while left < right
    // Bounds invariant - simplified
    invariant 0 <= left <= a.Length
    invariant -1 <= right < a.Length
    // CRITICAL: Mathematical relationship - left and right move symmetrically
    invariant left + right == a.Length - 1
    // Part 1: Elements on the left (already swapped) are reversed
    invariant forall i :: 0 <= i < left ==> a[i] == old(a[a.Length - 1 - i])
    // Part 2: Elements on the right (already swapped) are reversed
    invariant forall i :: right < i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
    // Part 3: Elements in the middle (not yet swapped) remain unchanged
    invariant forall i :: left <= i <= right ==> a[i] == old(a[i])
  {
    // Swap a[left] and a[right]
    var temp := a[left];
    a[left] := a[right];
    a[right] := temp;
    
    left := left + 1;
    right := right - 1;
  }
}

// Test method to demonstrate usage
method TestReverseArray()
{
  var arr := new int[5];
  arr[0], arr[1], arr[2], arr[3], arr[4] := 1, 2, 3, 4, 5;
  
  ReverseArray(arr);
  
  assert arr[0] == 5;
  assert arr[1] == 4;
  assert arr[2] == 3;
  assert arr[3] == 2;
  assert arr[4] == 1;
}

// Test with even-length array
method TestReverseArrayEven()
{
  var arr := new int[4];
  arr[0], arr[1], arr[2], arr[3] := 10, 20, 30, 40;
  
  ReverseArray(arr);
  
  assert arr[0] == 40;
  assert arr[1] == 30;
  assert arr[2] == 20;
  assert arr[3] == 10;
}

// Test with single element (edge case)
method TestReverseArraySingle()
{
  var arr := new int[1];
  arr[0] := 42;
  
  ReverseArray(arr);
  
  assert arr[0] == 42;
}

// Test with empty array (edge case)
method TestReverseArrayEmpty()
{
  var arr := new int[0];
  
  ReverseArray(arr);
  
  assert arr.Length == 0;
}