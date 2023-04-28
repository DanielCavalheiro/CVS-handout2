datatype List<T> = Nil | Cons(head: T,tail: List<T>)
datatype Option<T> = None | Some(elem: T)

class Hashtable<K(==,!new),V(!new)> {
  var size : int;
  var data : array<List<(K,V)>>;

  function hash(key: K) : int

  function bucket(k: K,n: int) : int
    requires n > 0
  {
    hash(k) % n
  }

  constructor(n: int)
    requires n > 0
  {
    size := n;
    data := new List<(K,V)>[n];
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