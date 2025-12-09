
/*===============================================
  CS:5810 Formal Methods in Software Engineering
  Fall 2025

  Mini Project 3 - Part D

  Your name(s): Example solution
  ===============================================*/

// Auxiliary predicate
// isSorted(a, lo, hi) holds iff the elements of array a 
// from position lo to position hi - 1 are in non-decreasing order
predicate isSorted(a: array<int>, lo: int, hi: nat)
  reads a
{
  forall i:nat, j:nat :: lo <= i <= j < hi <= a.Length ==> a[i] <= a[j]
}

// BubbleSort(a) sorts the integer array a in place 
// using the bubble sort algorithm
method BubbleSort(a: array<int>)
  modifies a
  // requires a.Length >=1
  // a is sorted non-decreasingly at the end
  ensures isSorted(a, 0, a.Length)
  // a is a permutation of old(a) (no elements are added or removed)
  ensures multiset(old(a[..])) == multiset(a[..])
{
  var i := a.Length - 1;
  while i > 0
  decreases i
  invariant i < a.Length
  && (forall k :: 0 <= i < k < a.Length  ==> a[k] >= a[i] )
  && (a.Length > i+1 ==> (forall k :: 0 <= k < (i+1)  ==> a[i+1] >= a[k] ))

  {
    var j := 0;
    while j < i
    decreases i - j
    invariant j < a.Length && (forall k :: 0 <= k < j  ==> a[j] >= a[k] ) && j <= i
    {
      if a[j] > a[j + 1] {
         a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    } 
    assert j == i;
    assert i < a.Length && (forall k :: 0 <= k < i  ==> a[i] >= a[k] );   
    i := i - 1;
  }
  assert i >= -1;
}
