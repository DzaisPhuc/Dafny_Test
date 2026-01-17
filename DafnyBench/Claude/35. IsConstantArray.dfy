method IsConstantArray(a: array<int>) returns (isConstant: bool)
  ensures isConstant <==> forall k :: 0 <= k < a.Length ==> a[k] == a[0]
{
  if a.Length == 0 {
    return true;
  }
  
  var value := a[0];
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] == value
  {
    if a[i] != value {
      return false;
    }
    i := i + 1;
  }
  
  return true;
}
