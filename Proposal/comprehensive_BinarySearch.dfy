method BinarySearch(a: array<int>, key: int, low: int, high: int) returns (index: int)
  requires 0 <= low <= high <= a.Length
  requires forall i, j :: low <= i < j < high ==> a[i] <= a[j]
  ensures low <= index < high ==> a[index] == key
  ensures index == -1 ==> forall i :: low <= i < high ==> a[i] != key
{
  var lo := low;
  var hi := high;
  while lo < hi
    invariant low <= lo <= hi <= high
    invariant forall i :: low <= i < lo ==> a[i] < key
    invariant forall i :: hi <= i < high ==> a[i] > key
  {
    var mid := (lo + hi) / 2;
    if a[mid] < key {
      lo := mid + 1;
    } else if a[mid] > key {
      hi := mid;
    } else {
      return mid;
    }
  }
  return -1;
}