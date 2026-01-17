method CheckIfSorted(a: array<int>) returns (isSorted: bool)
  ensures isSorted <==> forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
{
  if a.Length <= 1 {
    return true;
  }
  
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k - 1] <= a[k]
  {
    if a[i - 1] > a[i] {
      return false;
    }
    i := i + 1;
  }
  
  return true;
}
