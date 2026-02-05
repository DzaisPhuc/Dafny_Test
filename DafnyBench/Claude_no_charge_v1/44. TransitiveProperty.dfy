lemma TransitiveProperty(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i < j < k < a.Length
  requires forall m, n :: 0 <= m < n < a.Length ==> a[m] <= a[n]
  ensures a[i] <= a[k]
{
  // Dafny can prove this automatically
}

method VerifyTransitive(a: array<int>)
  requires forall m :: 0 <= m < a.Length - 1 ==> a[m] <= a[m + 1]
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall p, q :: 0 <= p < q < i ==> a[p] <= a[q]
  {
    var j := i + 1;
    while j < a.Length
      invariant i < j <= a.Length
      invariant forall p :: 0 <= p < i ==> a[p] <= a[j - 1]
    {
      assert a[i] <= a[j];
      j := j + 1;
    }
    i := i + 1;
  }
}
