method FindAllEvens(a: array<int>) returns (evens: seq<int>)
  ensures forall k :: 0 <= k < |evens| ==> evens[k] % 2 == 0
  ensures forall k :: 0 <= k < |evens| ==> exists j :: 0 <= j < a.Length && evens[k] == a[j]
{
  evens := [];
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < |evens| ==> evens[k] % 2 == 0
    invariant forall k :: 0 <= k < |evens| ==> exists j :: 0 <= j < i && evens[k] == a[j]
  {
    if a[i] % 2 == 0 {
      evens := evens + [a[i]];
    }
    i := i + 1;
  }
}
