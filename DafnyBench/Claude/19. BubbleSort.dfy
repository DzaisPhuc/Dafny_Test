method BubbleSort(a: array<int>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
{
  var n := a.Length;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant forall k, l :: n - i <= k < l < n ==> a[k] <= a[l]
    invariant forall k, l :: 0 <= k < n - i <= l < n ==> a[k] <= a[l]
  {
    var j := 0;
    while j < n - i - 1
      invariant 0 <= j <= n - i - 1
      invariant forall k :: 0 <= k <= j ==> a[k] <= a[j + 1]
    {
      if a[j] > a[j + 1] {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
