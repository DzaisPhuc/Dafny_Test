method FindMaximumIndex(a: array<int>) returns (maxIdx: int)
  requires a.Length > 0
  ensures 0 <= maxIdx < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[maxIdx] >= a[k]
{
  maxIdx := 0;
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant 0 <= maxIdx < i
    invariant forall k :: 0 <= k < i ==> a[maxIdx] >= a[k]
  {
    if a[i] > a[maxIdx] {
      maxIdx := i;
    }
    i := i + 1;
  }
}
