method PalindromeChecker(a: array<int>) returns (isPalindrome: bool)
  ensures isPalindrome <==> forall k :: 0 <= k < a.Length ==> a[k] == a[a.Length - 1 - k]
{
  var left := 0;
  var right := a.Length - 1;
  
  while left < right
    invariant 0 <= left <= right + 1 <= a.Length
    invariant forall k :: 0 <= k < left ==> a[k] == a[a.Length - 1 - k]
    invariant forall k :: right < k < a.Length ==> a[k] == a[a.Length - 1 - k]
  {
    if a[left] != a[right] {
      return false;
    }
    left := left + 1;
    right := right - 1;
  }
  
  return true;
}
