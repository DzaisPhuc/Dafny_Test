// Tìm vị trí CUỐI CÙNG của phần tử x trong mảng
method FindLastIndex(a: array<int>, x: int) returns (index: int)
  ensures index >= 0 ==> 0 <= index < a.Length && a[index] == x
  ensures index >= 0 ==> forall k :: index < k < a.Length ==> a[k] != x
  ensures index == -1 ==> forall k :: 0 <= k < a.Length ==> a[k] != x
{
  index := -1;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant index >= 0 ==> 0 <= index < i && a[index] == x
    invariant index >= 0 ==> forall k :: index < k < i ==> a[k] != x
    invariant index == -1 ==> forall k :: 0 <= k < i ==> a[k] != x
  {
    if a[i] == x {
      index := i;
    }
    i := i + 1;
  }
}

// Test đơn giản
method TestSimple() {
  // Test 1: Tìm thấy ở cuối
  var a1 := new int[3] [1, 2, 3];
  var idx := FindLastIndex(a1, 3);
  assert idx == 2;
  
  // Test 2: Không tìm thấy
  var a2 := new int[3] [1, 2, 3];
  idx := FindLastIndex(a2, 5);
  assert idx == -1;
  
  // Test 3: Có nhiều giá trị giống nhau
  var a3 := new int[5] [1, 2, 1, 3, 1];
  idx := FindLastIndex(a3, 1);
  assert idx == 4;
}