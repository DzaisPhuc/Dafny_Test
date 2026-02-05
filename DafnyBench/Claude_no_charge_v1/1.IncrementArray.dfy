method IncrementArray(a: array<int>, k: int)
  requires a != null
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + k
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[j]) + k
    invariant forall j :: i <= j < a.Length ==> a[j] == old(a[j])
  {
    a[i] := a[i] + k;
    i := i + 1;
  }
}

// Test method to demonstrate usage
method TestIncrementArray()
{
  var arr := new int[5];
  arr[0], arr[1], arr[2], arr[3], arr[4] := 1, 2, 3, 4, 5;
  
  IncrementArray(arr, 10);
  
  assert arr[0] == 11;
  assert arr[1] == 12;
  assert arr[2] == 13;
  assert arr[3] == 14;
  assert arr[4] == 15;
}