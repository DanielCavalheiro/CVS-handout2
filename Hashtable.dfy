datatype List<T> = Nil | Cons(head: T,tail: List<T>)
datatype Option<T> = None | Some(elem: T)

class Hashtable<K(==,!new),V(!new)> {
    var size : int;
    var data : array<List<(K,V)>>;
    
    function hash(key: K) : int
    
    function bucket(k: K,n: int) : int
    
    constructor(n: int)

    method clear()

    method resize()

    function list_find (k:K, l:List<(K,V)>) : option<V>
        ensures match list_find(k,l) {
            case None => ∀ v • !mem((k,v),l)
            case Some(v) => mem((k,v),l)
        }
    {
        match l {
            case Nil => None
            case Cons((`k,v),xs) ⇒ if k=k` then Some(v) else list_find(k,xs)
        }
    }

    method find(k: K) returns (r: Option<V>)

    function list_remove(k: K,l: List<(K,V)>) : List<(K,V)>
        decreases l
        ensures ∀ `k , v • mem((`k,v),list_remove(k,l)) ⇐⇒ (mem((`k,v),l) && `k != k)
    {
        match l {
            case Nil ⇒ Nil
            case Cons((`k,v),xs) ⇒ if k=`k then list_remove(k,xs) else
            Cons((`k,v),list_remove(k,xs))
        }
    }

    method remove(k: K)

    method add(k: K,v: V)
}