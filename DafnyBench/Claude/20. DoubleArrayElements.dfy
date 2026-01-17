method DoubleArrayElements(a: array<int>)
  modifies a
  ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[k]) * 2
{
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[k]) * 2
    invariant forall k :: i <= k < a.Length ==> a[k] == old(a[k])
  {
    a[i] := a[i] * 2;
    i := i + 1;
  }
}
