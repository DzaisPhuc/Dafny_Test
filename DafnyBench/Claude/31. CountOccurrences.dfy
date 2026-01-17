method CountOccurrences(a: array<int>, target: int) returns (count: int)
  ensures count == CountOccurrencesSpec(a, target, a.Length)
{
  count := 0;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant count == CountOccurrencesSpec(a, target, i)
  {
    if a[i] == target {
      count := count + 1;
    }
    i := i + 1;
  }
}

function CountOccurrencesSpec(a: array<int>, target: int, n: int): int
  reads a
  requires 0 <= n <= a.Length
{
  if n == 0 then 0
  else (if a[n - 1] == target then 1 else 0) + CountOccurrencesSpec(a, target, n - 1)
}
