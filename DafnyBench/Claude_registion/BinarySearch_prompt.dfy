// Predicate để xác định mảng đã được sắp xếp tăng dần
predicate sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

method BinarySearch(a: array<int>, key: int) returns (index: int)
  requires sorted(a)
  ensures 0 <= index < a.Length ==> a[index] == key
  ensures index == -1 ==> key !in a[..]
  ensures index != -1 ==> key in a[..]
{
  var low := 0;
  var high := a.Length - 1;
  
  while low <= high
    // Structural invariants - duy trì quan hệ chặt chẽ giữa các chỉ số
    invariant 0 <= low <= high + 1 <= a.Length
    
    // Functional invariant - logic 'loop summary'
    invariant key in a[..] <==> key in a[low..high+1]
    
    // Negative invariants - loại trừ các phần đã tìm kiếm
    invariant forall k :: 0 <= k < low ==> a[k] != key
    invariant forall k :: high < k < a.Length ==> a[k] != key
  {
    // Tính toán mid an toàn, tránh overflow
    var mid := low + (high - low) / 2;
    
    if a[mid] == key {
      return mid;
    } else if a[mid] < key {
      // Key phải nằm ở nửa phải
      low := mid + 1;
    } else {
      // Key phải nằm ở nửa trái
      high := mid - 1;
    }
  }
  
  // Khi vòng lặp kết thúc: low > high
  // Từ functional invariant: key in a[..] <==> key in a[low..high+1]
  // Vì low > high nên a[low..high+1] là rỗng
  // Do đó key !in a[..]
  return -1;
}