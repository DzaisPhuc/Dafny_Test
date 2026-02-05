method LongestIncreasingSubseq(a: array<int>) returns (length: int)
  requires a.Length > 0
  ensures length >= 1
{
  var dp := new int[a.Length];
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
  {
    dp[i] := 1;
    i := i + 1;
  }
  
  i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < a.Length ==> dp[k] >= 1
  {
    var j := 0;
    while j < i
      invariant 0 <= j <= i
    {
      if a[j] < a[i] && dp[j] + 1 > dp[i] {
        dp[i] := dp[j] + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  length := 1;
  i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant length >= 1
  {
    if dp[i] > length {
      length := dp[i];
    }
    i := i + 1;
  }
}
