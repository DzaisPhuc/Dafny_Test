method SearchRange(a: array<int>, key: int, low: int, high: int) returns (index: int)
  requires 0 <= low <= high <= a.Length
  ensures low <= index < high ==> a[index] == key
  ensures index == -1 ==> forall i :: low <= i < high ==> a[i] != key
{
  var i := low;
  while i < high
  {
    if a[i] == key {
      return i;
    }
    i := i + 1;
  }
  return -1;
}