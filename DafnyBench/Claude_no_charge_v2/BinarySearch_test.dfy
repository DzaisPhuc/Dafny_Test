// Predicate để xác định mảng đã được sắp xếp tăng dần
predicate sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Phương thức Binary Search với đầy đủ các bất biến và postcondition
method BinarySearch(a: array<int>, key: int) returns (index: int)
  requires sorted(a)
  ensures 0 <= index < a.Length ==> a[index] == key
  ensures index == -1 ==> key !in a[..]
{
  var low := 0;
  var high := a.Length - 1;
  
  while low <= high
    // Bất biến cấu trúc: Đảm bảo các chỉ số hợp lệ
    invariant 0 <= low <= high + 1 <= a.Length
    
    // Functional Invariant: Key nằm trong mảng khi và chỉ khi nó nằm trong cửa sổ tìm kiếm
    invariant key in a[..] <==> key in a[low..high+1]
    
    // Negative Invariants: Các phần tử ngoài cửa sổ tìm kiếm không phải là key
    invariant forall k :: 0 <= k < low ==> a[k] != key
    invariant forall k :: high < k < a.Length ==> a[k] != key
  {
    // Tính mid an toàn, tránh overflow
    var mid := low + (high - low) / 2;
    
    if a[mid] == key {
      return mid;
    } else if a[mid] < key {
      // Key nằm ở nửa phải, loại bỏ nửa trái
      low := mid + 1;
    } else {
      // Key nằm ở nửa trái, loại bỏ nửa phải
      high := mid - 1;
    }
  }
  
  // Khi vòng lặp kết thúc: low > high
  // Từ các bất biến, ta biết key không có trong a[0..low) và a[high+1..a.Length)
  // Và low..high+1 là rỗng (vì low > high), nên key không có trong mảng
  return -1;
}

// Phương thức test để minh họa
method TestBinarySearch()
{
  var arr := new int[5];
  arr[0], arr[1], arr[2], arr[3], arr[4] := 1, 3, 5, 7, 9;
  
  var result1 := BinarySearch(arr, 5);
  assert result1 == 2;
  
  var result2 := BinarySearch(arr, 6);
  assert result2 == -1;
  
  var result3 := BinarySearch(arr, 1);
  assert result3 == 0;
  
  var result4 := BinarySearch(arr, 9);
  assert result4 == 4;
}