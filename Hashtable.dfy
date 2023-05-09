datatype List<T> = Nil | Cons(head: T,tail: List<T>)
datatype Option<T> = None | Some(elem: T)

class Hashtable<K(==,!new),V(!new)> {
  var size : int;
  var data : array<List<(K,V)>>;

  ghost var mapa : map<K,Option<V>>;

  //1. All key-value pairs are in the appropriate bucket list
  ghost predicate valid_hash(d:array<List<(K,V)>>, i:int)
    requires 0 <= i < d.Length
    reads d
  {
    forall k, v :: mem((k,v), d[i]) ==> bucket(k, d.Length) == i
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
    (k in m && m[k] == Some(v)) <==> mem((k,v), d[b])
  }
  ghost predicate valid_map()
    reads this, data
    requires 0 < data.Length
  {
    forall k, v :: valid_data(k,v,mapa,data)
  }

  ghost predicate valid()
    reads this, data
  {
    0 < data.Length && valid_pairs_bucket() && valid_map()
  }

  function hash(key: K) : int

  function bucket(k: K,n: int) : int
    requires n > 0
  {
    hash(k) % n
  }

  constructor(n: int)
    requires n > 0
    ensures 0 < data.Length
    ensures valid()
    ensures mapa == map[] && fresh(data)
  {
    size := 0;
    data := new List<(K,V)>[n](_ => Nil);
    mapa := map[];
  }

  method clear()
    requires valid()
    modifies this, data
    ensures mapa == map[]
    ensures fresh(data)
  {
    mapa := map[];
    var i:int := 0;
    var new_data := new List<(K,V)>[data.Length](_ => Nil);
    data := new_data;
    size := 0;
  }

  method rehash(arr: array<List<(K,V)>>, l : List<(K,V)>, index : int)


  method resize()
    

  ghost function mem<T>(x:T, l:List<T>) : bool {
    match l {
      case Nil => false
      case Cons(y,xs) => x==y || mem(x,xs)
    }
  }

  ghost function length<T>(l:List<T>) : int {
    match l {
      case Nil => 0
      case Cons(_,xs) => 1 + length(xs)
    } }

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
    requires valid()
    ensures valid()
    ensures match r {
              case None => forall v :: !mem((k,v),data[bucket(k,data.Length)])
              case Some(v) => mem((k,v),data[bucket(k,data.Length)])
            }
  {
    var b := bucket(k, data.Length);
    r := list_find(k, data[b]);
  }


  function list_remove<K(==,!new),V(!new)>(k:K,l:List<(K,V)>) : List<(K,V)>
    decreases l
    ensures forall k' , v :: mem((k',v),list_remove(k,l)) <==>
                             (mem((k',v),l) && k != k')
  {
    match l {
      case Nil => Nil
      case Cons((k',v),xs) => if k==k' then list_remove(k,xs) else
      Cons((k',v),list_remove(k,xs))
    } 
  }

  method remove(k: K)
    modifies  data, `size, `mapa
    requires valid()
    ensures valid()
    ensures k !in mapa || (k in mapa && mapa[k] == None)
  {

    var b := bucket(k, data.Length);

    match list_find(k, data[b]) {
      case None => {
        assert forall v :: !mem((k,v),data[bucket(k,data.Length)]);
        assert forall k',v':: valid_data(k', v', mapa,data) && ((k' in mapa && mapa[k'] == Some(v')) <==> mem((k',v'), data[bucket(k', data.Length)]));
        assert forall i:: 0 <= i < data.Length ==> valid_hash(data,i);
        assert k !in mapa || (k in mapa && mapa[k] == None);
      }
      case Some(v) => {
        assert forall k',v':: valid_data(k', v', mapa,data) && ((k' in mapa && mapa[k'] == Some(v')) <==> mem((k',v'),data[bucket(k', data.Length)]));   
        assert forall i:: 0 <= i < data.Length ==> valid_hash(data,i) && forall k, v :: mem((k,v), data[i]) ==> bucket(k, data.Length) == i;

        data[b] := list_remove(k, data[b]);
        mapa := mapa[k := None];
        size := size - 1;
       
      }
    }
  }

  method add(k: K,v: V)
    modifies  data, `size, `mapa
    requires valid()
    ensures valid()
    ensures k in mapa && mapa[k] == Some(v)
  {
    remove(k);
    var b := bucket(k, data.Length);
    //size := size + 1; // prof disse para nao utilizar size
    assert forall k',v':: valid_data(k', v', mapa,data) && ((k' in mapa && mapa[k'] == Some(v')) <==> mem((k',v'), data[bucket(k', data.Length)]));
    assert forall i:: 0 <= i < data.Length ==> valid_hash(data,i) && forall k, v :: mem((k,v), data[i]) ==> bucket(k, data.Length) == i;

    var old_list := data[b];
    
    data[b] := Cons((k,v), old_list);
    mapa := mapa[k := Some(v)];
    //assert mem((k,v), data[b]) && k in mapa;
    //assert bucket(k, data.Length) == b && mem((k,v), data[b]);
    //assert valid_data(k,v,mapa,data);


  }
}