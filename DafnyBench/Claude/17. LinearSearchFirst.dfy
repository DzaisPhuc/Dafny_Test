method LinearSearchFirst(a: array<int>, target: int) returns (index: int)
  ensures index >= 0 ==> index < a.Length && a[index] == target
  ensures index >= 0 ==> forall k :: 0 <= k < index ==> a[k] != target
  ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != target
{
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] != target
  {
    if a[i] == target {
      return i;
    }
    i := i + 1;
  }
  
  return -1;
}
