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

    // Ensure elements beyond position + 1 remain unchanged and sorted
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
