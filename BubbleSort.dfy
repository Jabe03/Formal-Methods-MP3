
/*===============================================
  CS:5810 Formal Methods in Software Engineering
  Fall 2025

  Mini Project 3 - Part D

  Your name(s): Mitchell Piehl and Joshua Bergthold
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
  ghost var old_a_mset: multiset<int> := multiset(a[..]);
  var i := a.Length - 1;

  while i > 0
  decreases i
  invariant i < a.Length
  && isSorted(a, i+1, a.Length) //sorted condition
  && (a.Length > i+1 ==> (forall k :: 0 <= k < (i+1)  ==> a[i+1] >= a[k] )) //frame
  &&  old_a_mset == multiset(a[..]) //permutation condition
  {
    var j := 0;
    while j < i
    decreases i - j
    invariant j < a.Length && (forall k :: 0 <= k < j  ==> a[j] >= a[k] ) //sorted condition
    && j <= i 
    && isSorted(a, i+1, a.Length) //frame
    && (a.Length > i+1 ==> (forall k :: 0 <= k < (i+1)  ==> a[i+1] >= a[k] )) //frame 
    &&  old_a_mset == multiset(a[..]) //permutation condition
    {
      
      if a[j] > a[j + 1] {
         a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }  
    i := i - 1;
  }
}
