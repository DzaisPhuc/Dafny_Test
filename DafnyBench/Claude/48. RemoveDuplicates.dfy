method RemoveDuplicates(a: array<int>) returns (newLength: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  modifies a
  ensures 0 <= newLength <= a.Length
  ensures forall i, j :: 0 <= i < j < newLength ==> a[i] < a[j]
  ensures forall k :: 0 <= k < newLength ==> exists m :: 0 <= m < a.Length && a[k] == old(a[m])
{
  if a.Length == 0 {
    return 0;
  }
  
  var i := 1;
  var j := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 1 <= j <= i
    invariant forall k, l :: 0 <= k < l < j ==> a[k] < a[l]
  {
    if a[i] != a[j - 1] {
      a[j] := a[i];
      j := j + 1;
    }
    i := i + 1;
  }
  
  newLength := j;
}
