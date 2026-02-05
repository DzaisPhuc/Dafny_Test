method MatrixMultiplication(a: array2<int>, b: array2<int>) returns (c: array2<int>)
  requires a.Length1 == b.Length0
  ensures c.Length0 == a.Length0
  ensures c.Length1 == b.Length1
  ensures forall i, j :: 0 <= i < c.Length0 && 0 <= j < c.Length1 ==>
    c[i, j] == dotProduct(a, b, i, j, a.Length1)
{
  c := new int[a.Length0, b.Length1];
  var i := 0;
  
  while i < a.Length0
    invariant 0 <= i <= a.Length0
  {
    var j := 0;
    while j < b.Length1
      invariant 0 <= j <= b.Length1
    {
      var sum := 0;
      var k := 0;
      while k < a.Length1
        invariant 0 <= k <= a.Length1
      {
        sum := sum + a[i, k] * b[k, j];
        k := k + 1;
      }
      c[i, j] := sum;
      j := j + 1;
    }
    i := i + 1;
  }
}

function dotProduct(a: array2<int>, b: array2<int>, i: int, j: int, n: int): int
  reads a, b
  requires 0 <= i < a.Length0 && 0 <= j < b.Length1
  requires n == a.Length1 == b.Length0
{
  if n == 0 then 0
  else a[i, n - 1] * b[n - 1, j] + dotProduct(a, b, i, j, n - 1)
}
