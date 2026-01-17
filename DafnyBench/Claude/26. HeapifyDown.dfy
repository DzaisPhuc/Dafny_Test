method HeapifyDown(a: array<int>, i: int, n: int)
  requires 0 <= i < n <= a.Length
  modifies a
  ensures forall k :: 0 <= k < n && 2 * k + 1 < n ==> a[k] >= a[2 * k + 1]
  ensures forall k :: 0 <= k < n && 2 * k + 2 < n ==> a[k] >= a[2 * k + 2]
{
  var largest := i;
  var left := 2 * i + 1;
  var right := 2 * i + 2;
  
  if left < n && a[left] > a[largest] {
    largest := left;
  }
  
  if right < n && a[right] > a[largest] {
    largest := right;
  }
  
  if largest != i {
    a[i], a[largest] := a[largest], a[i];
  }
}
