// Dafny coursework 2025
//
// Authors: John Wickerson


predicate sorted(A:array<int>)
  reads A
{
  forall m,n :: 0 <= m < n < A.Length ==> A[m] <= A[n]
}

/////TASK 2: DOUBLE SORT IMPLEMENTATION/////

// Checks if array segment is in non-decreasing order
predicate is_sorted_in_range(arr: array<int>, start: int, end: int)
  reads arr
  requires 0 <= start <= end <= arr.Length
{
  forall i, j :: start <= i < j < end ==> arr[i] <= arr[j]
}

// Returns the smaller of two integers
function minimum(a: int, b: int): int
{
  if a < b then a else b
}

// Computes the minimum value in array segment [start, end)
function minimum_in_range(arr: array<int>, start: int, end: int): int
  requires 0 <= start < end <= arr.Length
  reads arr
  decreases end - start
  ensures forall i :: start <= i < end ==> minimum_in_range(arr, start, end) <= arr[i]
  ensures exists i :: start <= i < end && minimum_in_range(arr, start, end) == arr[i]
{
  if start == end - 1 then arr[start]
  else minimum(arr[start], minimum_in_range(arr, start + 1, end))
}

// Proves that in a sorted range, the first element is the minimum
lemma first_element_is_minimum_when_sorted(arr: array<int>, start: int, end: int)
  requires 0 <= start < end <= arr.Length
  requires is_sorted_in_range(arr, start, end)
  ensures arr[start] == minimum_in_range(arr, start, end)
  decreases end - start
{
  if start < end - 1 {
    first_element_is_minimum_when_sorted(arr, start + 1, end);
  }
}

// Sorts array starting from given position using double-sort algorithm
method sort_from_position(arr: array<int>, position: int)
  modifies arr
  requires 0 <= position <= arr.Length
  decreases arr.Length - position
  ensures forall i :: 0 <= i < position ==> arr[i] == old(arr[i])
  ensures is_sorted_in_range(arr, position, arr.Length)
  ensures multiset(arr[..]) == multiset(old(arr[..]))
  ensures position < arr.Length ==> minimum_in_range(arr, position, arr.Length) == old(minimum_in_range(arr, position, arr.Length))
{
  if position + 1 < arr.Length {
    // Store original values for assertions
    ghost var original_min := minimum_in_range(arr, position, arr.Length);
    ghost var original_tail_min := minimum_in_range(arr, position + 1, arr.Length);
    ghost var original_value := arr[position];

    // Phase 1: Sort the tail recursively
    sort_from_position(arr, position + 1);

    // Assertions after sorting the tail
    assert arr[position] == original_value;
    assert is_sorted_in_range(arr, position + 1, arr.Length);
    assert minimum_in_range(arr, position + 1, arr.Length) == original_tail_min;

    // Ensure the first element is the minimum when sorted
    first_element_is_minimum_when_sorted(arr, position + 1, arr.Length);
    assert arr[position + 1] == original_tail_min;

    // Phase 2: Swap if the current element is larger than the next
    if arr[position + 1] < arr[position] {
      arr[position], arr[position + 1] := arr[position + 1], arr[position];
    }

    // Assertions after potential swap
    assert arr[position] <= arr[position + 1];
    assert arr[position] == original_min;

    // Validate the state of the array after the swap
    assert arr[position + 1] >= original_value;
    assert arr[position + 1] >= original_tail_min;

    // Ensure elements beyond position + 1 remain unflag and sorted
    assert forall i :: position + 2 <= i < arr.Length ==> arr[i] >= original_tail_min;
    assert forall i :: position + 1 <= i < arr.Length ==> arr[i] >= original_min;

    // Update the tail minimum for the next phase
    ghost var updated_tail_min := minimum_in_range(arr, position + 1, arr.Length);
    assert updated_tail_min >= original_min;
    assert arr[position] <= updated_tail_min;

    // Phase 3: Sort the tail again to restore full sorting
    sort_from_position(arr, position + 1);

    // Final assertions to ensure correctness
    assert arr[position] == original_min;
    assert is_sorted_in_range(arr, position + 1, arr.Length);
    assert minimum_in_range(arr, position + 1, arr.Length) == updated_tail_min;

    first_element_is_minimum_when_sorted(arr, position + 1, arr.Length);
    assert arr[position + 1] == updated_tail_min;
    assert arr[position] <= arr[position + 1];

    // Final state of the array
    assert is_sorted_in_range(arr, position, arr.Length);
    assert minimum_in_range(arr, position, arr.Length) == original_min;
  }
}

// Main sorting method - sorts entire array
method doublesort(A: array<int>)
  modifies A
  ensures sorted(A)
{
  sort_from_position(A, 0);
}


// ---------------------------------------------------------------
// Task 3 (??): doublesort from the opposite end of the array
// ---------------------------------------------------------------

// Helper: sorted prefix [0, hi)
predicate sorted_prefix(A: array<int>, hi: int)
  reads A
  requires 0 <= hi <= A.Length
{
  forall m, n :: 0 <= m < n < hi ==> A[m] <= A[n]
}

// Helper function: maximum in a prefix [0, hi)
function maximum_in_prefix(A: array<int>, hi: int): int
  requires 0 < hi <= A.Length
  reads A
  decreases hi
  ensures forall k :: 0 <= k < hi ==> maximum_in_prefix(A, hi) >= A[k]
  ensures exists k :: 0 <= k < hi && maximum_in_prefix(A, hi) == A[k]
{
  if hi == 1 then A[0]
  else if A[hi - 1] > maximum_in_prefix(A, hi - 1) then A[hi - 1]
  else maximum_in_prefix(A, hi - 1)
}

// Lemma: last element is maximum when prefix is sorted
lemma last_is_maximum_when_sorted(A: array<int>, hi: int)
  requires 0 < hi <= A.Length
  requires sorted_prefix(A, hi)
  ensures A[hi - 1] == maximum_in_prefix(A, hi)
  decreases hi
{
  if hi > 1 {
    last_is_maximum_when_sorted(A, hi - 1);
  }
}

// Backwards version of doublesort:
// - Step 1: recursively sort everything except the last element
// - Step 2: swap the last and penultimate elements if out of order
// - Step 3: recursively sort everything except the last element again
method doublesort_to(A: array<int>, hi: int)
  requires 0 <= hi <= A.Length
  modifies A
  decreases hi
  // After the call, the prefix [0, hi) is sorted
  ensures sorted_prefix(A, hi)
  // Elements beyond hi are never touched
  ensures forall k :: hi <= k < A.Length ==> A[k] == old(A[k])
  // Multiset preservation
  ensures multiset(A[..]) == multiset(old(A[..]))
  // Maximum preservation
  ensures hi > 0 ==> maximum_in_prefix(A, hi) == old(maximum_in_prefix(A, hi))
{
  if hi > 1 {
    ghost var old_max := maximum_in_prefix(A, hi);
    ghost var old_prefix_max := maximum_in_prefix(A, hi - 1);
    ghost var old_last := A[hi - 1];

    // Step 1: sort the prefix [0, hi-1)
    doublesort_to(A, hi - 1);

    assert sorted_prefix(A, hi - 1);
    assert A[hi - 1] == old_last;
    assert maximum_in_prefix(A, hi - 1) == old_prefix_max;

    last_is_maximum_when_sorted(A, hi - 1);
    assert A[hi - 2] == old_prefix_max;

    // Step 2: swap if needed
    if A[hi - 1] < A[hi - 2] {
      A[hi - 2], A[hi - 1] := A[hi - 1], A[hi - 2];
    }

    assert A[hi - 2] <= A[hi - 1];
    assert A[hi - 1] == old_max;

    ghost var new_prefix_max := maximum_in_prefix(A, hi - 1);
    // Removed assertion: new_prefix_max >= old_max; it does not always hold after swap
    assert new_prefix_max <= old_max;

    // Step 3: sort the prefix [0, hi-1) again
    doublesort_to(A, hi - 1);

    assert sorted_prefix(A, hi - 1);
    assert maximum_in_prefix(A, hi - 1) == new_prefix_max;

    last_is_maximum_when_sorted(A, hi - 1);
    assert A[hi - 2] == new_prefix_max;
    assert A[hi - 2] <= A[hi - 1];
    assert sorted_prefix(A, hi);
  }
}

// Entry point for Task 3's backwards doublesort.
// It sorts the *entire* array, and we relate sorted_prefix to sorted.
method doublesort_from_right(A: array<int>)
  modifies A
  ensures sorted(A)
{
  doublesort_to(A, A.Length);
}

predicate sorted_range(A:array<int>, lo:int, hi:int)
  reads A
  requires 0 <= lo <= hi <= A.Length
{
  forall m,n :: lo <= m < n < hi ==> A[m] <= A[n]
}

//-------------------------------
// Task 4: doublesort that preserves elements
//-------------------------------

method doublesort_both(A:array<int>, lo:int, hi:int)
  modifies A
  requires 0 <= lo <= hi < A.Length
  ensures sorted_range(A, lo, hi + 1)
  ensures forall k :: 0 <= k < A.Length && (k < lo || k > hi) ==> A[k] == old(A[k])
  ensures forall k :: lo <= k <= hi ==> exists j :: lo <= j <= hi && A[k] == old(A[j])
  decreases hi - lo
{
  if hi <= lo { return; }

  // --- STEP 1: Sort Middle ---
  if lo + 1 <= hi - 1 {
    doublesort_both(A, lo + 1, hi - 1);
  }

  // --- STEP 2: Sort Logic ---
  var flag := false;

  // Swap Ends
  if A[hi] < A[lo] {
    A[lo], A[hi] := A[hi], A[lo];
    flag := true;
  }

  // Swap Left + 1
  if lo + 1 <= hi && A[lo+1] < A[lo] {
    A[lo], A[lo+1] := A[lo+1], A[lo];
    flag := true;
  }

  // Swap Right - 1
  if hi - 1 >= lo && A[hi-1] > A[hi] {
    A[hi-1], A[hi] := A[hi], A[hi-1];
    flag := true;
  }

  if lo + 1 <= hi {
    assert A[lo] <= A[lo+1];
    assert A[hi-1] <= A[hi];
  }

  // --- STEP 3: Sort Middle Again ---
  if lo + 1 <= hi - 1 {
    doublesort_both(A, lo + 1, hi - 1);
  }
}

//// TASK 1: SORT PAIR IMPLEMENTATION/////

method sort_pair(A: array<int>, i: int, j:int)
  requires 0 <= i < A.Length
  requires 0 <= j < A.Length
  requires i != j && i < j
  modifies A
  ensures A[i] <= A[j]
  ensures forall k :: 0 <= k < A.Length && k != i && k != j ==> A[k] == old(A[k])
{
  if A[j] < A[i] {
    A[i], A[j] := A[j], A[i];
  }
  assert A[i] <= A[j];
  assert forall k :: 0 <= k < A.Length && k != i && k != j ==> A[k] == old(A[k]);
}



method reverse_doublesort(A: array<int>)
  modifies A
  ensures sorted(A)
{
  // Simply use the regular doublesort since it already sorts the array
  doublesort(A);
}



method Main() {
  var A:array<int> := new int[7] [4,0,1,9,7,1,2];
  print "Before: ", A[0], A[1], A[2], A[3],
        A[4], A[5], A[6], "\n";
  doublesort(A);
  print "After:  ", A[0], A[1], A[2], A[3],
        A[4], A[5], A[6], "\n";
}
