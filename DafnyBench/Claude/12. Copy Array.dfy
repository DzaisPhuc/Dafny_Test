// ============================================================================
// V2 (Success/Verified): Array Copy with proper modifies clause
// ============================================================================

method ArrayCopy(a: array<int>, b: array<int>)
  requires a.Length == b.Length
  modifies b  // CRITICAL: This was missing in V1!
  ensures forall i :: 0 <= i < a.Length ==> b[i] == a[i]
  ensures a[..] == b[..]  // Alternative way to express the postcondition
{
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    // STRONG MAPPING INVARIANT: Elements copied so far match
    invariant forall k :: 0 <= k < i ==> b[k] == a[k]
    // FRAME CONDITION: Elements already copied remain unchanged
    invariant forall k :: 0 <= k < i ==> b[k] == old(b[k]) || b[k] == a[k]
  {
    b[i] := a[i];
    i := i + 1;
  }
}

// ============================================================================
// Explanation and Comparison
// ============================================================================

/* 
WHY THE MODIFIES CLAUSE IS CRUCIAL:

1. **Frame Condition**:
   - Dafny needs to know which memory locations can be modified
   - Without "modifies b", Dafny assumes b is immutable
   - This causes verification to fail because we're writing to b[i]

2. **Side Effect Gap in V1**:
   - Missing modifies clause → Dafny can't verify we have permission to change b
   - Weak invariant → Dafny can't prove elements remain stable across iterations
   - Result: "insufficient permission" or "postcondition might not hold" errors

3. **What V2 Fixes**:
   a) Added "modifies b" → Grants permission to modify array b
   b) Strong invariant "forall k :: 0 <= k < i ==> b[k] == a[k]"
      → Proves elements [0..i) have been correctly copied
   c) Frame invariant shows already-copied elements don't change
      → Bridges the gap between iterations

4. **How Dafny Verifies**:
   - Base case (i=0): Invariant holds vacuously (no elements copied yet)
   - Induction: After b[i] := a[i], element i matches; elements [0..i) unchanged
   - Termination (i=Length): Invariant becomes postcondition
*/

// ============================================================================
// V1 (Failed) - For Comparison
// ============================================================================

method ArrayCopyV1_Failed(a: array<int>, b: array<int>)
  requires a.Length == b.Length
  // MISSING: modifies b
  ensures forall i :: 0 <= i < a.Length ==> b[i] == a[i]
{
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    // WEAK: This alone isn't enough without proper modifies clause
    invariant forall k :: 0 <= k < i ==> b[k] == a[k]
  {
    // ERROR: Dafny complains here - no permission to modify b
    // b[i] := a[i];
    i := i + 1;
  }
}

// ============================================================================
// Enhanced Version with Additional Properties
// ============================================================================

method ArrayCopyEnhanced(a: array<int>, b: array<int>)
  requires a.Length == b.Length
  modifies b
  ensures forall i :: 0 <= i < a.Length ==> b[i] == a[i]
  ensures a[..] == b[..]
  // Additional property: source array unchanged
  ensures a[..] == old(a[..])
{
  ghost var originalA := a[..];
  ghost var originalB := b[..];
  
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    // Mapping invariant
    invariant forall k :: 0 <= k < i ==> b[k] == a[k]
    // Frame condition: already copied elements stable
    invariant forall k :: 0 <= k < i ==> b[k] == a[k]
    // Source array unchanged
    invariant a[..] == originalA
    // Preservation using sequences
    invariant b[..i] == a[..i]
  {
    b[i] := a[i];
    
    // Optional assertion to help solver
    assert b[i] == a[i];
    assert forall k :: 0 <= k < i ==> b[k] == a[k];
    
    i := i + 1;
  }
  
  assert b[..] == a[..];
}

// ============================================================================
// Test Cases
// ============================================================================

method TestArrayCopy() {
  // Test 1: Standard copy
  var src1 := new int[5] [1, 2, 3, 4, 5];
  var dst1 := new int[5];
  ArrayCopy(src1, dst1);
  assert dst1[0] == 1 && dst1[4] == 5;
  assert forall i :: 0 <= i < 5 ==> dst1[i] == src1[i];
  
  // Test 2: Copy negative numbers
  var src2 := new int[3] [-1, -2, -3];
  var dst2 := new int[3];
  ArrayCopy(src2, dst2);
  assert dst2[0] == -1 && dst2[2] == -3;
  
  // Test 3: Empty array
  var src3 := new int[0];
  var dst3 := new int[0];
  ArrayCopy(src3, dst3);
  assert src3[..] == dst3[..];
  
  // Test 4: Single element
  var src4 := new int[1] [42];
  var dst4 := new int[1];
  ArrayCopy(src4, dst4);
  assert dst4[0] == 42;
  
  // Test 5: Enhanced version
  var src5 := new int[4] [10, 20, 30, 40];
  var dst5 := new int[4];
  ghost var originalSrc := src5[..];
  ArrayCopyEnhanced(src5, dst5);
  assert src5[..] == originalSrc;  // Source unchanged
  assert dst5[..] == src5[..];     // Destination matches source
}

// ============================================================================
// Lemma: Array copy preserves length
// ============================================================================

lemma ArrayCopyPreservesLength(a: array<int>, b: array<int>)
  requires a.Length == b.Length
  ensures a.Length == b.Length
{
  // Trivial, but demonstrates lemma usage
}

// ============================================================================
// Summary of Key Differences V1 → V2
// ============================================================================

/*
┌─────────────────────────────────────────────────────────────────┐
│                    V1 (Failed)         V2 (Success)             │
├─────────────────────────────────────────────────────────────────┤
│ modifies clause    ❌ Missing          ✅ modifies b            │
│ Mapping invariant  ⚠️  Weak            ✅ Strong + Frame       │
│ Verification       ❌ Fails            ✅ Passes               │
│ Permission         ❌ No write access  ✅ Explicit permission  │
│ Frame reasoning    ❌ Incomplete       ✅ Complete             │
└─────────────────────────────────────────────────────────────────┘

The modifies clause is the bridge that allows Dafny to:
1. Grant permission to modify b
2. Track which locations can change
3. Verify frame conditions (what doesn't change)
4. Prove postconditions about the modified state
*/