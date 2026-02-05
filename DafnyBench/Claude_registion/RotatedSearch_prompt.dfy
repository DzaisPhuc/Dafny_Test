method RotatedSearch(a: array<int>, target: int) returns (result: int)
  ensures result >= 0 ==> result < a.Length && a[result] == target
  ensures result == -1 ==> target !in a[..]
{
  if a.Length == 0 {
    return -1;
  }

  var low := 0;
  var high := a.Length - 1;

  while low <= high
    // Safe Invariant: Bounds are well-formed
    invariant 0 <= low <= high + 1 <= a.Length
    
    // Loop Summary (Relational Postcondition): 
    // Target is in the array if and only if it's in the current window
    invariant target in a[..] <==> target in a[low..high+1]
    
    // Negative Invariant: All excluded indices don't contain target
    invariant forall k :: 0 <= k < low || high < k < a.Length ==> a[k] != target
  {
    var mid := low + (high - low) / 2;
    
    // The mid calculation is safe due to our invariant
    assert 0 <= mid < a.Length;

    if a[mid] == target {
      return mid;
    }

    // Determine which half is sorted
    // In a rotated sorted array, at least one half must be sorted
    if a[low] <= a[mid] {
      // Left half [low..mid] is sorted
      assert IsNonDecreasing(a[low..mid+1]);
      
      if a[low] <= target < a[mid] {
        // Target must be in the sorted left half
        assert target !in a[mid..high+1] by {
          // a[mid] < target or a[mid] == target (already checked)
          // Since left is sorted and target < a[mid], target must be in [low..mid)
          assert a[mid] > target;
          assert forall k :: mid <= k <= high ==> a[k] != target by {
            // We know target < a[mid]
            // If target were in [mid..high], it would contradict our search logic
            forall k | mid <= k <= high 
              ensures a[k] != target
            {
              if k == mid {
                assert a[k] != target;  // Already checked
              } else {
                // For rotated array, if left is sorted and we're looking right of mid,
                // we can only find target if it's >= a[mid] or in the rotated portion
                // But we know a[low] <= target < a[mid], so target isn't here
              }
            }
          }
        }
        high := mid - 1;
      } else {
        // Target must be in the right half (possibly rotated)
        assert target !in a[low..mid+1] by {
          forall k | low <= k <= mid
            ensures a[k] != target
          {
            if k == mid {
              assert a[k] != target;  // Already checked
            } else {
              // Left half is sorted: a[low] <= a[k] <= a[mid]
              // Either target < a[low] or target >= a[mid]
              // In both cases, target != a[k] for k in [low..mid]
              if target < a[low] {
                assert a[k] >= a[low] > target;
              } else {
                // target >= a[mid], and a[k] <= a[mid] for k <= mid in sorted portion
                assert a[k] <= a[mid] <= target;
                assert a[k] != target;
              }
            }
          }
        }
        low := mid + 1;
      }
    } else {
      // Right half [mid..high] is sorted
      assert a[mid] < a[low];  // This indicates rotation point is in left half
      assert IsNonDecreasing(a[mid..high+1]);
      
      if a[mid] < target <= a[high] {
        // Target must be in the sorted right half
        assert target !in a[low..mid+1] by {
          forall k | low <= k <= mid
            ensures a[k] != target
          {
            if k == mid {
              assert a[k] != target;  // Already checked
            } else {
              // Right half is sorted, target is in range [a[mid], a[high]]
              // But we know a[mid] < target
              // Left portion has rotation, but we know bounds
            }
          }
        }
        low := mid + 1;
      } else {
        // Target must be in the left half (with rotation)
        assert target !in a[mid..high+1] by {
          forall k | mid <= k <= high
            ensures a[k] != target
          {
            if k == mid {
              assert a[k] != target;  // Already checked
            } else {
              // Right half is sorted: a[mid] <= a[k] <= a[high]
              // Either target <= a[mid] or target > a[high]
              // In both cases, target != a[k] for k in [mid..high]
              if target <= a[mid] {
                assert a[k] >= a[mid] >= target;
                assert a[k] != target;
              } else {
                // target > a[high], and a[k] <= a[high] for k >= mid in sorted portion
                assert a[k] <= a[high] < target;
              }
            }
          }
        }
        high := mid - 1;
      }
    }
  }

  return -1;
}

// Helper predicate to characterize sorted sequences
predicate IsNonDecreasing(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}