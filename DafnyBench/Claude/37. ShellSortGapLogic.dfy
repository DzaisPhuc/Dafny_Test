method ShellSortGapLogic(a: array<int>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
{
  var gap := a.Length / 2;
  
  while gap > 0
    invariant gap >= 0
  {
    var i := gap;
    while i < a.Length
      invariant gap <= i <= a.Length
    {
      var temp := a[i];
      var j := i;
      
      while j >= gap && a[j - gap] > temp
        invariant gap <= j <= i
      {
        a[j] := a[j - gap];
        j := j - gap;
      }
      
      a[j] := temp;
      i := i + 1;
    }
    gap := gap / 2;
  }
}
