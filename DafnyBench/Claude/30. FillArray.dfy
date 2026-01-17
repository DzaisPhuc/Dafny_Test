method FillArray(a: array<int>, value: int)
  modifies a
  ensures forall k :: 0 <= k < a.Length ==> a[k] == value
{
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] == value
  {
    a[i] := value;
    i := i + 1;
  }
}
