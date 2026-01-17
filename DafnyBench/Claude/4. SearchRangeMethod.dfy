// Predicate to check if an array is sorted
predicate IsSorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Helper method to find the first occurrence of target
method FindFirst(a: array<int>, target: int) returns (first: int)
  requires a != null
  requires IsSorted(a)
  ensures first == -1 <==> (forall k :: 0 <= k < a.Length ==> a[k] != target)
  ensures 0 <= first < a.Length ==> a[first] == target
  ensures 0 <= first < a.Length ==> forall k :: 0 <= k < first ==> a[k] < target
  ensures 0 <= first < a.Length ==> forall k :: 0 <= k < a.Length && a[k] == target ==> first <= k
{
  if a.Length == 0 {
    return -1;
  }
  
  var low := 0;
  var high := a.Length - 1;
  var result := -1;
  
  while low <= high
    invariant 0 <= low <= a.Length
    invariant -1 <= high < a.Length
    invariant result == -1 || (0 <= result < a.Length && a[result] == target)
    // Elimination: elements outside [low, high] are wrong
    invariant forall i :: 0 <= i < low ==> a[i] < target
    invariant forall i :: high < i < a.Length ==> a[i] > target
    // If result is set, no element before it equals target
    invariant result != -1 ==> forall k :: 0 <= k < result ==> a[k] < target
    // Critical: if target exists, it's either found or in [low, high]
    invariant (exists k :: 0 <= k < a.Length && a[k] == target) ==> 
              (result != -1 || (exists k :: low <= k <= high && a[k] == target))
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    
    if a[mid] == target {
      result := mid;
      high := mid - 1;
    } else if a[mid] < target {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  
  // When loop exits: low > high, so [low, high] is empty
  // From invariants: all elements are either < target or > target or already found
  // Therefore if result == -1, no target exists
  
  return result;
}

// Helper method to find the last occurrence of target
method FindLast(a: array<int>, target: int) returns (last: int)
  requires a != null
  requires IsSorted(a)
  ensures last == -1 <==> (forall k :: 0 <= k < a.Length ==> a[k] != target)
  ensures 0 <= last < a.Length ==> a[last] == target
  ensures 0 <= last < a.Length ==> forall k :: last < k < a.Length ==> a[k] > target
  ensures 0 <= last < a.Length ==> forall k :: 0 <= k < a.Length && a[k] == target ==> k <= last
{
  if a.Length == 0 {
    return -1;
  }
  
  var low := 0;
  var high := a.Length - 1;
  var result := -1;
  
  while low <= high
    invariant 0 <= low <= a.Length
    invariant -1 <= high < a.Length
    invariant result == -1 || (0 <= result < a.Length && a[result] == target)
    // Elimination: elements outside [low, high] are wrong
    invariant forall i :: 0 <= i < low ==> a[i] < target
    invariant forall i :: high < i < a.Length ==> a[i] > target
    // If result is set, no element after it equals target
    invariant result != -1 ==> forall k :: result < k < a.Length ==> a[k] > target
    // Critical: if target exists, it's either found or in [low, high]
    invariant (exists k :: 0 <= k < a.Length && a[k] == target) ==> 
              (result != -1 || (exists k :: low <= k <= high && a[k] == target))
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    
    if a[mid] == target {
      result := mid;
      low := mid + 1;
    } else if a[mid] < target {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  
  return result;
}

// Main method to find the range [first, last] of target
method SearchRange(a: array<int>, target: int) returns (first: int, last: int)
  requires a != null
  requires IsSorted(a)
  ensures (first == -1) <==> (last == -1)
  ensures first == -1 <==> (forall k :: 0 <= k < a.Length ==> a[k] != target)
  ensures first != -1 ==> 0 <= first <= last < a.Length
  ensures first != -1 ==> a[first] == target && a[last] == target
  ensures first != -1 ==> forall k :: 0 <= k < first ==> a[k] < target
  ensures first != -1 ==> forall k :: last < k < a.Length ==> a[k] > target
  ensures first != -1 ==> forall k :: first <= k <= last ==> a[k] == target
  ensures first != -1 ==> forall k :: 0 <= k < a.Length && a[k] == target ==> first <= k <= last
{
  first := FindFirst(a, target);
  
  if first == -1 {
    last := -1;
    return;
  }
  
  last := FindLast(a, target);
  
  // Prove all elements in [first, last] equal target
  assert a[first] == target;
  assert a[last] == target;
  
  forall k | first <= k <= last
    ensures a[k] == target
  {
    // From FindFirst: all k < first have a[k] < target
    // From FindLast: all k > last have a[k] > target
    // From IsSorted: a[first] <= a[k] <= a[last]
    // Since a[first] == target and a[last] == target
    // We have target <= a[k] <= target
    // Therefore a[k] == target
    
    assert forall i :: 0 <= i < first ==> a[i] < target;
    assert forall i :: last < i < a.Length ==> a[i] > target;
    
    // a[k] cannot be < target (else by sorted, k < first, contradiction)
    // a[k] cannot be > target (else by sorted, k > last, contradiction)
    // Therefore a[k] == target
    
    // Proof by sorted property
    assert a[first] <= a[k] <= a[last];  // by IsSorted
    assert a[first] == target && a[last] == target;
    
    // If a[k] != target, then either a[k] < target or a[k] > target
    if a[k] < target {
      // Then a[k] < target = a[first]
      // But by sorted, first <= k implies a[first] <= a[k]
      // Contradiction!
      assert a[first] <= a[k];
      assert false;
    }
    if a[k] > target {
      // Then a[k] > target = a[last]
      // But by sorted, k <= last implies a[k] <= a[last]
      // Contradiction!
      assert a[k] <= a[last];
      assert false;
    }
  }
}

// Test with multiple occurrences
method TestSearchRange()
{
  var arr := new int[10];
  arr[0], arr[1], arr[2], arr[3], arr[4] := 1, 2, 2, 2, 2;
  arr[5], arr[6], arr[7], arr[8], arr[9] := 2, 3, 4, 5, 5;
  
  var first, last := SearchRange(arr, 2);
  assert first != -1;
  assert 0 <= first <= last < arr.Length;
  assert arr[first] == 2;
  assert arr[last] == 2;
}

// Test with single occurrence
method TestSearchRangeSingle()
{
  var arr := new int[5];
  arr[0], arr[1], arr[2], arr[3], arr[4] := 1, 3, 5, 7, 9;
  
  var first, last := SearchRange(arr, 5);
  assert first != -1;
  assert 0 <= first <= last < arr.Length;
  assert arr[first] == 5;
  assert arr[last] == 5;
}

// Test with target not found
method TestSearchRangeNotFound()
{
  var arr := new int[5];
  arr[0], arr[1], arr[2], arr[3], arr[4] := 1, 3, 5, 7, 9;
  
  var first, last := SearchRange(arr, 6);
  assert first == -1;
  assert last == -1;
}

// Test with all elements being target
method TestSearchRangeAll()
{
  var arr := new int[4];
  arr[0], arr[1], arr[2], arr[3] := 5, 5, 5, 5;
  
  var first, last := SearchRange(arr, 5);
  assert first != -1;
  assert 0 <= first <= last < arr.Length;
  assert arr[first] == 5;
  assert arr[last] == 5;
}

// Test with empty array
method TestSearchRangeEmpty()
{
  var arr := new int[0];
  
  var first, last := SearchRange(arr, 5);
  assert first == -1;
  assert last == -1;
}