method MergeSortedArrays(a: array<int>, b: array<int>) returns (c: array<int>)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  requires forall i, j :: 0 <= i < j < b.Length ==> b[i] <= b[j]
  ensures c.Length == a.Length + b.Length
  ensures forall i, j :: 0 <= i < j < c.Length ==> c[i] <= c[j]
{
  c := new int[a.Length + b.Length];
  var i := 0;
  var j := 0;
  var k := 0;
  
  while i < a.Length && j < b.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= j <= b.Length
    invariant k == i + j
    invariant forall m, n :: 0 <= m < n < k ==> c[m] <= c[n]
  {
    if a[i] <= b[j] {
      c[k] := a[i];
      i := i + 1;
    } else {
      c[k] := b[j];
      j := j + 1;
    }
    k := k + 1;
  }
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant k == i + j
  {
    c[k] := a[i];
    i := i + 1;
    k := k + 1;
  }
  
  while j < b.Length
    invariant 0 <= j <= b.Length
    invariant k == i + j
  {
    c[k] := b[j];
    j := j + 1;
    k := k + 1;
  }
}
