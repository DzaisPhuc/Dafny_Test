method ReverseArraySeq(a: array<int>)
  modifies a
  ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[a.Length - 1 - k])
{
  var left := 0;
  var right := a.Length - 1;
  
  while left < right
    invariant 0 <= left <= right + 1 <= a.Length
    invariant forall k :: 0 <= k < left ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k :: right < k < a.Length ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k :: left <= k <= right ==> a[k] == old(a[k])
  {
    a[left], a[right] := a[right], a[left];
    left := left + 1;
    right := right - 1;
  }
}
