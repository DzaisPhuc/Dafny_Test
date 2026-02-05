method BoyerMooreVoting(a: array<int>) returns (candidate: int)
  requires a.Length > 0
  requires exists x :: CountOccurrences(a, x) > a.Length / 2
  ensures CountOccurrences(a, candidate) > a.Length / 2
{
  candidate := a[0];
  var count := 0;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant count >= 0
  {
    if count == 0 {
      candidate := a[i];
      count := 1;
    } else if a[i] == candidate {
      count := count + 1;
    } else {
      count := count - 1;
    }
    i := i + 1;
  }
}

function CountOccurrences(a: array<int>, x: int): int
  reads a
{
  if a.Length == 0 then 0
  else (if a[0] == x then 1 else 0) + CountOccurrences(a[1..], x)
}
