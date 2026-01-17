function power(x: int, n: nat): int
{
  if n == 0 then 1
  else x * power(x, n - 1)
}

method PowerFunction(x: int, n: nat) returns (res: int)
  ensures res == power(x, n)
{
  res := 1;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant res == power(x, i)
  {
    res := res * x;
    i := i + 1;
  }
}
