method RemoveElementInPlace(a: array<int>, target: int) returns (newLength: int)
  modifies a
  ensures 0 <= newLength <= a.Length
  ensures forall k :: 0 <= k < newLength ==> a[k] != target
  ensures forall k :: 0 <= k < newLength ==> exists j :: 0 <= j < a.Length && a[k] == old(a[j])
{
  var i := 0;
  var j := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= j <= i
    invariant forall k :: 0 <= k < j ==> a[k] != target
    invariant forall k :: 0 <= k < j ==> exists m :: 0 <= m < i && a[k] == old(a[m])
  {
    if a[i] != target {
      a[j] := a[i];
      j := j + 1;
    }
    i := i + 1;
  }
  
  newLength := j;
}
