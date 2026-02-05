method FilterEvenNumbers(a: array<int>) returns (result: array<int>, length: int)
  ensures 0 <= length <= a.Length
  ensures length <= result.Length
  ensures forall k :: 0 <= k < length ==> result[k] % 2 == 0
  ensures forall k :: 0 <= k < length ==> exists j :: 0 <= j < a.Length && result[k] == a[j]
{
  var count := 0;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant count >= 0
  {
    if a[i] % 2 == 0 {
      count := count + 1;
    }
    i := i + 1;
  }
  
  result := new int[count];
  length := 0;
  i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant 0 <= length <= count
    invariant forall k :: 0 <= k < length ==> result[k] % 2 == 0
  {
    if a[i] % 2 == 0 {
      result[length] := a[i];
      length := length + 1;
    }
    i := i + 1;
  }
}
