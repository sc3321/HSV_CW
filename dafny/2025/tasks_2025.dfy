// Dafny coursework 2025
//
// Authors: John Wickerson


predicate sorted(A:array<int>)
  reads A
{
  forall m,n :: 0 <= m < n < A.Length ==> A[m] <= A[n]
}

method doublesort_from(A:array<int>, lo:int)
  modifies A
  requires 0 <= lo < A.Length 
  requires A != null
  decreases A.Length - lo
{
  if lo + 1 < A.Length {
    doublesort_from(A, lo + 1);
    if A[lo + 1] < A[lo] {
      A[lo], A[lo + 1] := A[lo + 1], A[lo];
    }
    assert 0 <= lo + 1 <= A.Length; 
    doublesort_from(A, lo + 1);
  }
}

method doublesort(A:array<int>)
  ensures sorted(A)
  requires A.Length > 0
{
  doublesort_from(A, 0);
}

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

method Main() {
  var A:array<int> := new int[7] [4,0,1,9,7,1,2];
  print "Before: ", A[0], A[1], A[2], A[3],
        A[4], A[5], A[6], "\n";
  doublesort(A);
  print "After:  ", A[0], A[1], A[2], A[3],
        A[4], A[5], A[6], "\n";
}
