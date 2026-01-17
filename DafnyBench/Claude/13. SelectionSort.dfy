method SelectionSort(a: array<int>)
  modifies a
  ensures sorted(a, 0, a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    // Prefix [0..i) is sorted
    invariant sorted(a, 0, i)
    // Elements in [0..i) are <= all elements in [i..Length)
    invariant forall k, m :: 0 <= k < i <= m < a.Length ==> a[k] <= a[m]
    // Multiset preservation
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    // Find minimum element in [i..Length)
    var minIndex := i;
    var j := i + 1;
    
    while j < a.Length
      invariant i <= minIndex < j <= a.Length
      // minIndex points to minimum in [i..j)
      invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
      // Array unchanged during inner loop
      invariant a[..] == old(a[..])
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if a[j] < a[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    // After inner loop: minIndex points to minimum in [i..Length)
    assert forall k :: i <= k < a.Length ==> a[minIndex] <= a[k];
    
    // Swap a[i] with a[minIndex]
    if i != minIndex {
      a[i], a[minIndex] := a[minIndex], a[i];
    }
    
    // Key bridging assertion: after swap, a[i] is minimum of original [i..Length)
    // This bridges the gap between inner and outer loop invariants
    assert forall k :: i < k < a.Length ==> a[i] <= a[k];
    
    i := i + 1;
  }
}

// Helper predicate: checks if array segment is sorted
predicate sorted(a: array<int>, from: int, to: int)
  reads a
  requires 0 <= from <= to <= a.Length
{
  forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}