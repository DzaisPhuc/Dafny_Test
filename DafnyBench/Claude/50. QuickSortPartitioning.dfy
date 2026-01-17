method QuickSortPartitioning(a: array<int>, low: int, high: int) returns (pivotIndex: int)
  requires 0 <= low < high <= a.Length
  modifies a
  ensures low <= pivotIndex < high
  ensures forall k :: low <= k < pivotIndex ==> a[k] <= a[pivotIndex]
  ensures forall k :: pivotIndex < k < high ==> a[k] >= a[pivotIndex]
{
  var pivot := a[high - 1];
  var i := low;
  var j := low;
  
  while j < high - 1
    invariant low <= j <= high - 1
    invariant low <= i <= j
    invariant forall k :: low <= k < i ==> a[k] <= pivot
    invariant forall k :: i <= k < j ==> a[k] > pivot
  {
    if a[j] <= pivot {
      a[i], a[j] := a[j], a[i];
      i := i + 1;
    }
    j := j + 1;
  }
  
  a[i], a[high - 1] := a[high - 1], a[i];
  pivotIndex := i;
}
