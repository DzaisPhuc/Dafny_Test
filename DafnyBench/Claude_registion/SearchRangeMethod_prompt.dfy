// Predicate để xác định mảng đã được sắp xếp tăng dần
predicate sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Helper method: Tìm vị trí xuất hiện ĐẦU TIÊN của target
method FindFirst(a: array<int>, target: int) returns (result: int)
  requires sorted(a)
  // Completeness postconditions
  ensures result != -1 ==> 0 <= result < a.Length && a[result] == target
  ensures result != -1 ==> (result == 0 || a[result-1] < target)
  ensures result == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != target
  // Memory safety - read-only array
  ensures result != -1 ==> target in a[..]
{
  if a.Length == 0 {
    return -1;
  }

  var low := 0;
  var high := a.Length - 1;
  var candidate := -1;

  while low <= high
    // Structural invariants
    invariant 0 <= low <= high + 1 <= a.Length
    invariant candidate == -1 || (0 <= candidate < a.Length && a[candidate] == target)
    
    // Boundary (negative) invariants - các phần đã loại trừ
    invariant forall k :: 0 <= k < low ==> a[k] < target
    invariant forall k :: high < k < a.Length ==> a[k] > target || (a[k] == target && (candidate == -1 || k >= candidate))
    
    // Functional invariant - nếu target tồn tại, nó phải trong [low..high+1] hoặc đã tìm thấy
    invariant target in a[..] ==> (candidate != -1 || target in a[low..high+1])
    
    // Candidate correctness
    invariant candidate != -1 ==> (forall k :: 0 <= k < candidate ==> a[k] < target)
  {
    var mid := low + (high - low) / 2;
    
    if a[mid] == target {
      candidate := mid;
      // Tiếp tục tìm bên trái để tìm vị trí đầu tiên
      high := mid - 1;
    } else if a[mid] < target {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  
  return candidate;
}

// Helper method: Tìm vị trí xuất hiện CUỐI CÙNG của target
method FindLast(a: array<int>, target: int) returns (result: int)
  requires sorted(a)
  // Completeness postconditions
  ensures result != -1 ==> 0 <= result < a.Length && a[result] == target
  ensures result != -1 ==> (result == a.Length - 1 || a[result+1] > target)
  ensures result == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != target
  // Memory safety - read-only array
  ensures result != -1 ==> target in a[..]
{
  if a.Length == 0 {
    return -1;
  }

  var low := 0;
  var high := a.Length - 1;
  var candidate := -1;

  while low <= high
    // Structural invariants
    invariant 0 <= low <= high + 1 <= a.Length
    invariant candidate == -1 || (0 <= candidate < a.Length && a[candidate] == target)
    
    // Boundary (negative) invariants - các phần đã loại trừ
    invariant forall k :: 0 <= k < low ==> a[k] < target || (a[k] == target && (candidate == -1 || k <= candidate))
    invariant forall k :: high < k < a.Length ==> a[k] > target
    
    // Functional invariant - nếu target tồn tại, nó phải trong [low..high+1] hoặc đã tìm thấy
    invariant target in a[..] ==> (candidate != -1 || target in a[low..high+1])
    
    // Candidate correctness
    invariant candidate != -1 ==> (forall k :: candidate < k < a.Length ==> a[k] > target)
  {
    var mid := low + (high - low) / 2;
    
    if a[mid] == target {
      candidate := mid;
      // Tiếp tục tìm bên phải để tìm vị trí cuối cùng
      low := mid + 1;
    } else if a[mid] < target {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  
  return candidate;
}

// Main method: Tìm phạm vi [first, last] của target trong mảng
method SearchRange(a: array<int>, target: int) returns (first: int, last: int)
  requires sorted(a)
  // Completeness postconditions
  ensures first == -1 && last == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != target
  ensures first != -1 ==> 0 <= first <= last < a.Length
  ensures first != -1 ==> forall k :: first <= k <= last ==> a[k] == target
  ensures first != -1 ==> (first == 0 || a[first-1] < target)
  ensures last != -1 ==> (last == a.Length - 1 || a[last+1] > target)
  // Consistency
  ensures (first == -1) <==> (last == -1)
{
  first := FindFirst(a, target);
  
  if first == -1 {
    last := -1;
    return;
  }
  
  last := FindLast(a, target);
  
  // Assert để giúp verifier
  assert first != -1 && last != -1;
  assert a[first] == target && a[last] == target;
}

// Test method để minh họa
method TestSearchRange()
{
  var arr := new int[8] [1, 2, 3, 3, 3, 4, 5, 6];
  var first, last := SearchRange(arr, 3);
  assert first == 2 && last == 4;
  
  var first2, last2 := SearchRange(arr, 7);
  assert first2 == -1 && last2 == -1;
  
  var arr2 := new int[1] [5];
  var first3, last3 := SearchRange(arr2, 5);
  assert first3 == 0 && last3 == 0;
}