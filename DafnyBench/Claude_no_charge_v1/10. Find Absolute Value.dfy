method Abs(x: int) returns (y: int)
  ensures y >= 0
  ensures x >= 0 ==> y == x
  ensures x < 0 ==> y == -x
{
  if x >= 0 {
    y := x;
  } else {
    y := -x;
  }
}

// Test method to demonstrate correctness
method TestAbs() {
  var result: int;
  
  // Test positive number
  result := Abs(42);
  assert result == 42;
  assert result >= 0;
  
  // Test negative number
  result := Abs(-17);
  assert result == 17;
  assert result >= 0;
  
  // Test zero
  result := Abs(0);
  assert result == 0;
  assert result >= 0;
  
  // Test edge cases
  result := Abs(1);
  assert result == 1;
  
  result := Abs(-1);
  assert result == 1;
}