method FindMinimum(a: array<int>) returns (min: int)
  requires a.Length > 0
  ensures forall k :: 0 <= k < a.Length ==> min <= a[k]
  ensures exists k :: 0 <= k < a.Length && a[k] == min
{
  min := a[0];
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> min <= a[k]
    invariant exists k :: 0 <= k < i && a[k] == min
  {
    if a[i] < min {
      min := a[i];
    }
    i := i + 1;
  }
}
