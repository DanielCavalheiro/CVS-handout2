datatype List<T> = Nil | Cons(head: T,tail: List<T>)
datatype Option<T> = None | Some(elem: T)

class Hashtable<K(==,!new),V(!new)> {
  var size : int;
  var data : array<List<(K,V)>>;
  
  ghost var mapa : map<K,Option<V>>;

  //1. All key-value pairs are in the appropriate bucket list
  ghost predicate valid_hash_aux(len:int, l:List<(K,V)>, i:int)
    requires 0 <= i < len
  {
    match l {
      case Nil => true
      case Cons((k,v),xs) => bucket(k, len) == i && valid_hash_aux(len, xs, i)
    }
  }
  ghost predicate valid_hash(d:array<List<(K,V)>>, i:int)
    requires 0 <= i < d.Length
    reads d
  {
    valid_hash_aux(d.Length, d[i], i)
  }
  ghost predicate valid_pairs_bucket()
    reads this, data
  {
    forall i :: 0 <= i < data.Length ==> valid_hash(data, i)
  }

  //2. The hastable and its contents implement exactly a map
  ghost predicate valid_data(k:K,v:V,m:map<K,Option<V>>, d:array<List<(K,V)>>)
    reads this, d
    requires 0 < d.Length
  {
    var b := bucket(k, d.Length);
    (k in m ==> m[k] == Some(v)) <==> (list_find(k, d[b]) == Some(v))
  }
  ghost predicate valid_map()
    reads this, data
    requires size == data.Length && size > 0
  {
    forall k,v :: k in mapa <==> valid_data(k,v,mapa,data)
  }

  ghost predicate valid()
    reads this, data
    requires size == data.Length && size > 0
  {
    valid_pairs_bucket() && valid_map()
  }

  function hash(key: K) : int

  function bucket(k: K,n: int) : int
    requires n > 0
  {
    hash(k) % n
  }

  constructor(n: int)
    requires n > 0
    ensures size == n && data.Length == size
    ensures valid()
    ensures mapa == map[] && fresh(data)
  {
    size := n;
    data := new List<(K,V)>[n](_ => Nil);
    mapa := map[];
  }

  method clear()

  method resize()

  function mem<T(==)> (k: T, l: List<T>) : bool
  {
    match l
    case Nil => false
    case Cons(k', t) =>
      if(k' == k) then true else mem(k, t)
  }

  function list_find (k:K, l:List<(K,V)>) : Option<V>
    ensures match list_find(k,l) {
              case None => forall v :: !mem((k,v),l)
              case Some(v) => mem((k,v),l)
            }
  {
    match l {
      case Nil => None
      case Cons((k',v),xs) => if k==k' then Some(v) else list_find(k,xs)
    }
  }

  method find(k: K) returns (r: Option<V>)

  function list_remove(k: K,l: List<(K,V)>) : List<(K,V)>
    decreases l
    ensures forall k' , v :: mem((k',v),list_remove(k,l)) <==> (mem((k',v),l) && k' != k)
  {
    match l {
      case Nil => Nil
      case Cons((k',v),xs) => if k==k' then list_remove(k,xs) else
      Cons((k',v),list_remove(k,xs))
    }
  }

  method remove(k: K)

  method add(k: K,v: V)
}