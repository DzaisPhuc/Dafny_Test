method MatrixRotation(a: array2<int>)
  requires a.Length0 == a.Length1
  modifies a
  ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==>
    a[i, j] == old(a[a.Length0 - 1 - j, i])
{
  var n := a.Length0;
  var i := 0;
  
  while i < n / 2
    invariant 0 <= i <= n / 2
  {
    var j := i;
    while j < n - i - 1
      invariant i <= j <= n - i - 1
    {
      var temp := a[i, j];
      a[i, j] := a[n - 1 - j, i];
      a[n - 1 - j, i] := a[n - 1 - i, n - 1 - j];
      a[n - 1 - i, n - 1 - j] := a[j, n - 1 - i];
      a[j, n - 1 - i] := temp;
      j := j + 1;
    }
    i := i + 1;
  }
}
