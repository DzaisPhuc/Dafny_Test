method LongestCommonPrefix(strs: array<seq<char>>) returns (prefix: seq<char>)
  requires strs.Length > 0
  ensures forall i :: 0 <= i < strs.Length ==> |prefix| <= |strs[i]|
  ensures forall i :: 0 <= i < strs.Length ==> prefix <= strs[i]
{
  if strs.Length == 0 {
    return [];
  }
  
  prefix := [];
  var i := 0;
  
  while i < |strs[0]|
    invariant 0 <= i <= |strs[0]|
    invariant forall k :: 0 <= k < strs.Length ==> prefix <= strs[k]
  {
    var ch := strs[0][i];
    var j := 1;
    var allMatch := true;
    
    while j < strs.Length
      invariant 1 <= j <= strs.Length
    {
      if i >= |strs[j]| || strs[j][i] != ch {
        allMatch := false;
        break;
      }
      j := j + 1;
    }
    
    if !allMatch {
      return prefix;
    }
    
    prefix := prefix + [ch];
    i := i + 1;
  }
}
