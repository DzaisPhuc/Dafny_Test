function factorial(n: nat): nat
{
  if n == 0 then 1
  else n * factorial(n - 1)
}

method FactorialIterative(n: nat) returns (result: nat)
  ensures result == factorial(n)
{
  result := 1;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant result == factorial(i - 1)
  {
    result := result * i;
    i := i + 1;
  }
}
