

/*===============================================
  CS:5810 Formal Methods in Software Engineering
  Fall 2025

  Project 3 -- Part A

  Your name(s): Mitchell Piehl and Josh Bergthold
  ===============================================*/

include "Option.dfy"
include "List.dfy"

module Map {
  
  import opened L = List
  import opened O = Option

  type Entry<T(!new)> = (int, T)

  // Auxiliary function that can be used in contracts
  function key<T(!new)>(e: Entry<T>): int
  {
    match e
    case (k, _) =>  k
  }

   // Auxiliary function that can be used in contracts
 function value<T(!new)>(e: Entry<T>): T
  {
    match e
    case (_, v) =>  v
  }

  type Map<T(!new)> = List<Entry<T>>

  // entries(m) is the set of all the elements stored in m (no contract needed)
  ghost function entries<T(!new)>(m: Map<T>): set<Entry<T>>
  { L.elements(m) }


  ghost function keys2<T(!new)>(m: List<Entry<T>>): set<int>
    decreases m
    ensures isEmpty(m) <==> keys2(m) == {}
  {
    match m
    case Nil => {}
    case Cons((k, v), t) => {k} + keys2(t)
  }

  // A map m is valid iff, as a list, it contains no repeated elements and
  // every key in m has exactly one associated value (no contract needed) 
  ghost predicate isValid<T(!new)>(m: Map<T>)
  {
  match m
  case Nil => true
  case Cons(e, Nil) =>
    true
  case Cons((k,_), t) =>
    isValid(t) && k !in keys2(t)
  }

  // For every value type T, emptyMap<T>() is 
  // the empty map of elements of type T
  function emptyMap<T(!new)>(): Map<T> 
    ensures isValid(emptyMap<T>())
    ensures isEmpty(emptyMap<T>())
  { Nil }

  // isEmpty(m) is true iff m has no entries 
  predicate isEmpty<T(!new)>(m: Map<T>)
    ensures m == Nil <==> isEmpty(m)
  { m == Nil }

  // size(m) is the number of entries in m
  function size<T(==,!new)>(m: Map<T>): nat 
    requires isValid(m)
    ensures isEmpty(m) <==> size(m) == 0
    ensures !isEmpty(m) ==> size(m) > 0
    ensures size(m) == |keys(m)|
  {
    match m
    case Nil => 0
    case Cons(_, t) => 1 + size(t)
  }

  // keys(m) is the set of keys in m's entries
  function keys<T(!new)>(m: Map<T>): set<int>
    decreases m
    requires isValid(m)
    ensures isEmpty(m) <==> keys(m) == {}
    ensures keys(m) == keys2(m)
  {
    match m
    case Nil => {}
    case Cons((k, v), t) => {k} + keys(t)
  }

  // values(m) is the set of values in m's entries
  function values<T(!new)>(m: Map<T>): set<T>
    requires isValid(m)
    ensures isValid(m)

    ensures isEmpty(m) <==> values(m) == {}
    ensures |values(m)| <= size(m)

    ensures forall i: int :: (get(m, i) != None) <==> i in keys(m)
  {
    match m
    case Nil => {}
    case Cons((k, v), t) => {v} + values(t)    
  }

  // get(m, k) is the value associated to key k in m, if any.
  // More precisely, it is Some(v) if k has an associated value v,
  // and is None otherwhise.
  function get<T(!new)>(m: Map<T>, k: int): Option<T>
    requires isValid(m)
    ensures isValid(m)
    ensures (get(m,k) == None) <==> k !in keys(m)
    ensures (get(m,k) == None) <==> k !in keys2(m)
    
    ensures (get(m,k) != None) ==> 
    (k, (get(m,k)).val) in entries(m)
  {
    match m
    case Nil => None
    case Cons((n, v), t) => 
      if k == n then 
        Some(v) 
      else
        get(t, k)
  }

  // remove(m, k) is the map obtained from m by removing from it
  // the entry with key k, if any.
  function remove<T(!new)>(m: Map<T>, k: int): Map<T>
    requires isValid(m)
    ensures isValid(remove(m,k))
    ensures get(remove(m,k), k) == None
    ensures forall q: int :: q != k ==> get(remove(m,k), q) == get(m,q)

    ensures k !in keys(m) ==> size(remove(m,k)) == size(m) 
    ensures k in keys(m) ==> size(remove(m,k)) == size(m) -1
    ensures values(remove(m,k)) <= values(m)

    ensures keys(remove(m,k)) == keys(m) - {k}
  {
    match m
    case Nil => Nil
    case Cons((k', v'), t) => 
      if k == k' then
        t 
      else
        var m' := remove(t, k);
        put(m', k', v')
  }

  // put(m, k, v) is the map that associates key k with value v
  // and is othewise identical to m.
  function put<T(!new)>(m: Map<T>, k: int, v: T): Map<T>
    requires isValid(m)
    ensures isValid(put(m,k,v))

    ensures keys(put(m,k,v)) == keys(m) + {k}
    ensures v in values(put(m, k, v))
    ensures (k, v) in entries(put(m, k,v))
    ensures entries(put(m,k,v)) - {(k,v)} <= entries(m)
    // ensures (get(m,k) != None) ==> 
    //     (k, (get(m,k)).val) in entries(m) 
    // ensures (get(m,k) != None)==>
    //     entries(put(m,k,v)) - {(k,v)} == 
    //     (entries(m) - {(k, get(m,k).val)})
    // ensures get(m,k) == None ==> 
    //     entries(put(m,k,v)) - {(k,v)} == (entries(m))


    ensures get(put(m,k,v), k) == Some(v)
    ensures forall q :: q != k ==> get(put(m,k,v), q) == get(m, q)

    ensures k in keys(m) ==> size(put(m,k,v)) == size(m) 
    ensures k !in keys(m) ==> size(put(m,k,v)) == size(m) + 1
    ensures values(put(m, k, v)) <= values(m) + {v}
  {
    match m
    case Nil => Cons((k, v), Nil)
    case Cons((k', v'), t) => 
      if k != k' then
        Cons((k', v'), put(t, k, v))
      else 
        Cons((k', v), t) 
  }
}


// Test

import opened Option
import opened Map

method test() {
  var m: Map<string>;
  var vo: Option<string>;

  m := emptyMap();            assert isValid(m); assert isEmpty(m);
  m := put(m, 3, "Panda");    assert isValid(m); assert !isEmpty(m); assert entries(m) == { (3, "Panda") };
  m := put(m, 9, "Lion");     assert isValid(m); assert entries(m) == { (3, "Panda"), (9, "Lion") };
  vo := get(m, 3);            assert vo == Some("Panda");
  m := put(m, 3, "Bear");     assert isValid(m); assert entries(m) == { (3, "Bear"), (9, "Lion") };
  vo := get(m, 3);            assert vo == Some("Bear");
  vo := get(m, 9);            assert vo == Some("Lion");
  vo := get(m, 7);            assert vo == None;
  m := remove(m, 3);          assert isValid(m); assert entries(m) == { (9, "Lion") };
  vo := get(m, 3);            assert vo == None;
  vo := get(m, 9);            assert vo == Some("Lion");
} 
