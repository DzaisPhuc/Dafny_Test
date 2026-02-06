method InterpolationSearch(a: array<int>, key: int, low: int, high: int) returns (index: int)
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
    if a[lo] == a[hi - 1] {
      if a[lo] == key {
        return lo;
      } else {
        return -1;
      }
    }
    var pos := lo + (key - a[lo]) * (hi - lo) / (a[hi - 1] - a[lo]);
    if pos < lo || pos >= hi {
      return -1;
    }
    if a[pos] < key {
      lo := pos + 1;
    } else if a[pos] > key {
      hi := pos;
    } else {
      return pos;
    }
  }
  return -1;
}