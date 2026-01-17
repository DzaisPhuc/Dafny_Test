method InsertionSort(a: array<int>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
{
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k, l :: 0 <= k < l < i ==> a[k] <= a[l]
  {
    var key := a[i];
    var j := i - 1;
    
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant forall k :: j < k < i ==> a[k] > key
      invariant forall k, l :: 0 <= k < l <= j || j + 1 < k < l <= i ==> a[k] <= a[l]
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    
    a[j + 1] := key;
    i := i + 1;
  }
}
