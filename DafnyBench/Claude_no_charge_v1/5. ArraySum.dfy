// 1. Định nghĩa toán học: Tổng của chuỗi s
function TotalSum(s: seq<int>): int {
  if |s| == 0 then 0 
  else s[0] + TotalSum(s[1..]) // Lấy phần tử đầu + tổng phần còn lại
}

// 2. Hàm thực thi
method ComputeSum(a: array<int>) returns (res: int)
  ensures res == TotalSum(a[..]) // Đảm bảo kết quả cuối cùng đúng
{
  res := 0;
  var i := a.Length;

  // Bí kíp: Chạy ngược từ cuối mảng về 0 hoặc dùng Invariant cho phần còn lại
  // Ở đây ta dùng vòng lặp xuôi nhưng Invariant nhắm vào phần đuôi
  var k := 0;
  while k < a.Length
    invariant 0 <= k <= a.Length
    // Invariant: Tổng hiện tại + Tổng phần còn lại của mảng = Tổng toàn bộ mảng ban đầu
    invariant res + TotalSum(a[k..]) == TotalSum(a[..])
  {
    res := res + a[k];
    // Hint: Giúp Dafny hiểu TotalSum(a[k..]) = a[k] + TotalSum(a[k+1..])
    assert a[k..] == [a[k]] + a[k+1..]; 
    k := k + 1;
  }
}

// 3. Test case tối giản
method Test() {
  var a := new int[3] [1, 2, 3];
  var s := ComputeSum(a);
  assert s == 6;
}