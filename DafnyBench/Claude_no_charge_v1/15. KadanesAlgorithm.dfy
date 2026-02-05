method KadanesAlgorithm(a: array<int>) returns (maxSum: int)
  requires a.Length > 0
  ensures forall i, j :: 0 <= i <= j < a.Length ==> maxSum >= sum(a, i, j)
{
  maxSum := a[0];
  var currentSum := a[0];
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant currentSum >= 0 ==> forall k :: 0 <= k < i ==> maxSum >= a[k]
  {
    currentSum := if currentSum > 0 then currentSum + a[i] else a[i];
    maxSum := if currentSum > maxSum then currentSum else maxSum;
    i := i + 1;
  }
}

function sum(a: array<int>, i: int, j: int): int
  reads a
  requires 0 <= i <= j < a.Length
{
  if i == j then a[i]
  else a[i] + sum(a, i + 1, j)
}
