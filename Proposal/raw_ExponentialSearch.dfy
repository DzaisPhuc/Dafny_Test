method ExponentialSearch(a: array<int>, key: int, low: int, high: int) returns (index: int)
  requires 0 <= low <= high <= a.Length
  requires forall i, j :: low <= i < j < high ==> a[i] <= a[j]
  ensures low <= index < high ==> a[index] == key
  ensures index == -1 ==> forall i :: low <= i < high ==> a[i] != key
{
  if low >= high {
    return -1;
  }
  if a[low] == key {
    return low;
  }
  var bound := 1;
  while low + bound < high && a[low + bound] < key
    invariant low <= low + bound <= high
    invariant forall i :: low <= i < low + bound ==> a[i] < key
  {
    bound := bound * 2;
  }
  var lo := low + bound / 2;
  var hi := if low + bound < high then low + bound + 1 else high;
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