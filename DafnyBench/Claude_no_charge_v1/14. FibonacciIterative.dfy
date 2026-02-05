function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method FibonacciIterative(n: nat) returns (result: nat)
  ensures result == fib(n)
{
  if n == 0 {
    return 0;
  }
  if n == 1 {
    return 1;
  }
  
  var prev := 0;
  var curr := 1;
  var i := 2;
  
  while i <= n
    invariant 2 <= i <= n + 1
    invariant prev == fib(i - 2)
    invariant curr == fib(i - 1)
  {
    var temp := curr;
    curr := prev + curr;
    prev := temp;
    i := i + 1;
  }
  
  return curr;
}
