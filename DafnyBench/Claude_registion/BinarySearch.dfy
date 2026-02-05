// Binary Search in Dafny with formal verification

// Predicate to check if an array is sorted
predicate isSorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Binary search method that returns the index if found, -1 otherwise
method BinarySearch(a: array<int>, key: int) returns (index: int)
  requires isSorted(a)
  ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
  ensures 0 <= index < a.Length ==> a[index] == key
{
  var low := 0;
  var high := a.Length;
  
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < low ==> a[i] < key
    invariant forall i :: high <= i < a.Length ==> a[i] > key
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    
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

// Alternative: Binary search that returns a boolean indicating presence
method BinarySearchExists(a: array<int>, key: int) returns (found: bool)
  requires isSorted(a)
  ensures found <==> exists k :: 0 <= k < a.Length && a[k] == key
{
  var low := 0;
  var high := a.Length;
  
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < low ==> a[i] < key
    invariant forall i :: high <= i < a.Length ==> a[i] > key
    invariant (exists k :: 0 <= k < a.Length && a[k] == key) <==>
              (exists k :: low <= k < high && a[k] == key)
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    
    if a[mid] < key {
      low := mid + 1;
    } else if a[mid] > key {
      high := mid;
    } else {
      return true;
    }
  }
  
  return false;
}

// Test method demonstrating usage
method Main()
{
  var arr := new int[7] [1, 3, 5, 7, 9, 11, 13];
  
  var idx := BinarySearch(arr, 7);
  assert idx == 3;
  
  idx := BinarySearch(arr, 4);
  assert idx == -1;
  
  var found := BinarySearchExists(arr, 9);
  assert found == true;
  
  found := BinarySearchExists(arr, 10);
  assert found == false;
  
  print "Binary search verification successful!\n";
}
