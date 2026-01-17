method FillArray(a: array<int>, v: int)
  modifies a
  ensures forall k :: 0 <= k < a.Length ==> a[k] == v
{
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] == v
  {
    a[i] := v;
    i := i + 1;
  }
}

// Alternative implementation with decreasing loop
method FillArrayReverse(a: array<int>, v: int)
  modifies a
  ensures forall k :: 0 <= k < a.Length ==> a[k] == v
{
  var i := a.Length;
  
  while i > 0
    invariant 0 <= i <= a.Length
    invariant forall k :: i <= k < a.Length ==> a[k] == v
    decreases i
  {
    i := i - 1;
    a[i] := v;
  }
}

// Test method to verify correctness
method TestFillArray() {
  var a := new int[5] [1, 2, 3, 4, 5];
  
  FillArray(a, 42);
  
  assert a[0] == 42;
  assert a[1] == 42;
  assert a[2] == 42;
  assert a[3] == 42;
  assert a[4] == 42;
  assert forall k :: 0 <= k < a.Length ==> a[k] == 42;
  
  // Test with reverse fill
  var b := new int[3] [10, 20, 30];
  
  FillArrayReverse(b, 99);
  
  assert b[0] == 99;
  assert b[1] == 99;
  assert b[2] == 99;
  assert forall k :: 0 <= k < b.Length ==> b[k] == 99;
}

// Edge case: empty array
method TestEmptyArray() {
  var empty := new int[0];
  FillArray(empty, 7);
  assert forall k :: 0 <= k < empty.Length ==> empty[k] == 7;
}

// Edge case: single element
method TestSingleElement() {
  var single := new int[1];
  single[0] := 100;
  
  FillArray(single, 5);
  
  assert single[0] == 5;
  assert forall k :: 0 <= k < single.Length ==> single[k] == 5;
}