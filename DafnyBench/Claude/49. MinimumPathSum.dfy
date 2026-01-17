method MinimumPathSum(grid: array2<int>) returns (minSum: int)
  requires grid.Length0 > 0 && grid.Length1 > 0
  ensures minSum >= 0
{
  var m := grid.Length0;
  var n := grid.Length1;
  var dp := new int[m, n];
  
  dp[0, 0] := grid[0, 0];
  
  var i := 1;
  while i < m
    invariant 1 <= i <= m
  {
    dp[i, 0] := dp[i - 1, 0] + grid[i, 0];
    i := i + 1;
  }
  
  var j := 1;
  while j < n
    invariant 1 <= j <= n
  {
    dp[0, j] := dp[0, j - 1] + grid[0, j];
    j := j + 1;
  }
  
  i := 1;
  while i < m
    invariant 1 <= i <= m
  {
    j := 1;
    while j < n
      invariant 1 <= j <= n
    {
      var fromTop := dp[i - 1, j];
      var fromLeft := dp[i, j - 1];
      dp[i, j] := (if fromTop < fromLeft then fromTop else fromLeft) + grid[i, j];
      j := j + 1;
    }
    i := i + 1;
  }
  
  minSum := dp[m - 1, n - 1];
}
