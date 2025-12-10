/*===============================================
  CS:5810 Formal Methods in Software Engineering
  Fall 2025

  Mini Project 3 - Part C

  Your name(s): Mitchell Piehl and Joshua Bergthold
  ===============================================*/

include "Option.dfy"
include "List.dfy"
include "Map.dfy"

import opened M = Map
import opened Option

class UMap<T(!new,==)> {
  var entries : Map<T>
  // this.entrySet() is the set of all the entries in the map 
  ghost function entrySet(): set<Entry<T>>
    reads this
    requires isValid()
    ensures entrySet() == M.entries(entries)
    {
      L.elements(entries)
    }

  // this.keySet() is the set of all the keys in the map 
  ghost function keySet(): set<int>
    reads this
    requires isValid()
    ensures isEmpty() <==> keySet() == {}
    ensures keySet() == M.keys(entries)
  {
    M.keys(entries)
  }

  // this.valueSet() is the set of all the values in the map 
  ghost function valueSet(): set<T>
    reads this
    requires isValid()
    ensures isEmpty() <==> valueSet() == {}
    ensures valueSet() == M.values(entries)
    ensures |valueSet()| <= |keySet()|
  {
    M.values(entries)
  }

  // A map m is valid iff it contains no repeated elements and
  // every key in m has exactly one associated value (no requires or ensures needed) 
  ghost predicate isValid() 
    reads this
  {
    M.isValid(entries)
  }

  // this.hasValue(k) is true iff key k as a value in the map
  ghost predicate hasValue(k: int)
    reads this
    requires isValid()
    {
      k in keySet()
    }

  // this.isEmpty() is true iff the map contains no entries
  predicate isEmpty() 
    reads this
    requires isValid()
    ensures isEmpty() <==> |entrySet()| == 0
    {
      M.isEmpty(entries)
    }


  // constructor returns a (new) map with an empty set of entries.
  constructor ()
    ensures isValid()
    ensures entrySet() == {}
    ensures keySet() == {}
    ensures valueSet() == {}
    ensures isEmpty()
  {
    entries := M.emptyMap();
  }

  // this.size() returns the number of entries in the map
  method size() returns (s: nat) 
    requires isValid()
    ensures isEmpty() <==> s == 0
    ensures !isEmpty() ==> s > 0
    ensures s == |keySet()|
    ensures s == M.size(entries)
    {
      s := M.size(entries);
    }

  // this.get(k) returns the value associated to key k in the map, if any.
  // More precisely, it returns Some(v) if k has an associated value v,
  // and returns None otherwhise.
  method get(k: int) returns (vo: Option<T>)
   requires isValid()
    ensures isValid()
    ensures (vo ==  None) <==> k !in keySet()
    ensures vo == M.get(entries,k)
    ensures (vo != None) ==> (k, (vo).val) in entrySet()
    ensures forall v:T :: vo == Some(v) ==> (k,v) in entrySet()
  {
    vo := M.get(entries, k);
  }


  // this.put(k, v) changes the map so that key k is associated with value v.
  // Then it returns the value previously associated to k in the map, if any.
  // More precisely, it returns Some(v) if k had an associated value v,
  // and returns None otherwhise.
  method put(k: int, v: T) returns (old_vo: Option<T>) 
    requires isValid()
    ensures isValid()
    modifies this
    ensures keySet() == old(keySet()) + {k}
    ensures valueSet() <= old(valueSet()) + {v}
    ensures v in valueSet()

    ensures old_vo == old(M.get(entries, k))
    ensures old_vo != None ==> (k, old_vo.val) in old(entrySet())

    ensures entries == M.put(old(entries), k, v)
    {
      old_vo := get(k);
      entries := M.put(entries,k,v);
    }

  // this.remove(k) removes from the map the entry eith key k, if any.
  // Then it returns the value previously associated to k in the map, if any.
  // More precisely, it returns Some(v) if k had an associated value v,
  // and returns None otherwhise.
  method remove(k: int) returns (vo: Option<T>)
    requires isValid()
    ensures isValid()
    modifies this

    ensures keySet() == old(keySet()) - {k}
    ensures k in keySet() ==> valueSet() < old(valueSet())

    ensures vo == old(M.get(entries, k))
    ensures vo != None ==> (k, vo.val) in old(entrySet())
    ensures vo == None ==> (k) !in old(keySet())

    ensures M.get(entries, k) == None
    ensures forall q:int :: q != k ==> M.get(entries, q) == M.get(old(entries), q)
  {
    vo := get(k);
    entries := M.remove(entries, k);
  }
}
