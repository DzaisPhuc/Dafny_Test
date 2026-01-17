method BinarySearchStrict(a: array<int>, key: int) returns (index: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures index >= 0 ==> index < a.Length && a[index] == key
  ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
  var low := 0;
  var high := a.Length;
  
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall k :: 0 <= k < low ==> a[k] < key
    invariant forall k :: high <= k < a.Length ==> a[k] > key
  {
    var mid := (low + high) / 2;
    if a[mid] < key {
      low := mid + 1;
    } else if a[mid] > key {
      high := mid;
    } else {
      return mid;
    }
  }
  
  return -1;
}
