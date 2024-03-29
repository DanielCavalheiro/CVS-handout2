datatype List<T> = Nil | Cons(head: T,tail: List<T>)
datatype Option<T> = None | Some(elem: T)

class Hashtable<K(==,!new),V(!new)> {
  var size : int; //prof disse que size nao seria necessario para a prova
  var data : array<List<(K,V)>>;
  ghost var mapa : map<K,Option<V>>;
  ghost var Repr : set<object>;

  //1. All key-value pairs are in the appropriate bucket list
  ghost predicate valid_hash(d:array<List<(K,V)>>, i:int)
    requires 0 <= i < d.Length
    reads d
  {
    forall k, v :: mem((k,v), d[i]) ==> bucket(k, d.Length) == i
  }
  ghost predicate valid_pairs_bucket()
    reads this, Repr
  {
    data in Repr && forall i :: 0 <= i < data.Length ==> valid_hash(data, i)
  }

  //2. The hastable and its contents implement exactly a map
  ghost predicate valid_data(k:K,v:V,m:map<K,Option<V>>, d:array<List<(K,V)>>)
    reads d
    requires 0 < d.Length
  {
    var b := bucket(k, d.Length);
    (k in m && m[k] == Some(v)) <==> mem((k,v), d[b])
  }
  ghost predicate valid_map()
    reads this, Repr
    requires 0 < data.Length
  {
    data in Repr && forall k, v :: valid_data(k,v,mapa,data)
  }

  ghost predicate valid()
    reads this, Repr
  {
    this in Repr && data in Repr && 0 < data.Length && valid_pairs_bucket() && valid_map()
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
    ensures fresh(Repr - {this})
    ensures mapa == map[]
  {
    size := 0;
    data := new List<(K,V)>[n](_ => Nil);
    mapa := map[];
    Repr := {this, data};
  }

  method clear()
    requires valid()
    modifies Repr
    ensures mapa == map[]
    ensures fresh(Repr - old(Repr))
  {
    mapa := map[];
    var i:int := 0;
    var new_data := new List<(K,V)>[data.Length](_ => Nil);
    
    Repr := Repr - {data};
    data := new_data;
    Repr := Repr + {data};

    size := 0;
  }

  method rehash(arr: array<List<(K,V)>>, l : List<(K,V)>, oldSize : int, newSize : int, index : int)
    requires valid()
    requires 0 < oldSize == data.Length
    requires arr.Length == newSize == (oldSize * 2) + 1
    requires forall k,v :: mem((k,v), l) ==> bucket(k, oldSize) == index
    requires forall j :: 0 <= j < newSize ==> valid_hash(arr, j)
    requires forall k,v :: (
                           if 0 <= bucket(k, oldSize) < index then valid_data(k,v,mapa,arr)
                           else if bucket(k, oldSize) == index then (k in mapa && mapa[k] == Some(v))
                                                                    <==> mem((k,v), l) || mem((k,v), arr[bucket(k, newSize)])
                           else
                             !mem((k,v), arr[bucket(k, newSize)])
                             )
    ensures valid()
    ensures forall j :: 0 <= j < newSize ==> valid_hash(arr, j)
    ensures forall k,v :: if 0 <= bucket(k, oldSize) <= index then valid_data(k,v,mapa,arr)
                          else
                            !mem((k,v), arr[bucket(k, newSize)])
    modifies arr
    decreases l
  {
    match l {
      case Nil => return;
      case Cons((k,v), xs) => {
        var b := bucket(k, newSize);
        arr[b] := Cons((k,v), arr[b]);
        rehash(arr, xs, oldSize, newSize, index);
      }
    }
  }

  method resize()
    requires valid()
    ensures valid()
    ensures fresh(Repr - old(Repr))
    modifies Repr
  {
    var oldSize := data.Length;
    var newSize := (oldSize * 2) + 1;
    var arr := new List<(K,V)>[newSize](_ => Nil);
    var i: int := 0;
    while(i < oldSize)
      invariant Repr == old(Repr)
      invariant 0 <= i <= oldSize
      invariant arr != data
      invariant old(data) == data
      invariant oldSize == data.Length
      invariant arr.Length == newSize == (oldSize * 2) + 1
      invariant forall j :: 0 <= j < newSize ==> valid_hash(arr, j)
      invariant forall j:: 0 <= j < data.Length ==> valid_hash(data,j) && forall k, v :: mem((k,v), data[j]) ==> bucket(k, oldSize) == j
      invariant forall k, v :: if (0 <= bucket(k, oldSize) < i) then valid_data(k,v,mapa,arr) else !mem((k,v), arr[bucket(k, newSize)])
      
      modifies arr
    {
      assert forall k, v :: valid_data(k,v,mapa,data) && ((k in mapa && mapa[k] == Some(v)) <==> mem((k,v), data[bucket(k, data.Length)]));
      assert forall k,v :: (
                           if 0 <= bucket(k, data.Length) < i then valid_data(k,v,mapa,arr)
                           else if bucket(k, data.Length) == i then ((k in mapa && mapa[k] == Some(v)) <==> mem((k,v), data[i]) || mem((k,v), arr[bucket(k, arr.Length)]))
                           else
                             !mem((k,v), arr[bucket(k, arr.Length)])
                             );

      rehash(arr, data[i], oldSize, newSize, i);
      i := i + 1;
    }
    Repr := Repr - {data};
    data := arr;
    Repr := Repr + {data};
  }


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
    modifies Repr
    requires valid()
    ensures valid()
    ensures fresh(Repr - old(Repr))
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

        Repr := Repr - {data};
        data[b] := list_remove(k, data[b]);
        mapa := mapa[k := None];
        size := size - 1;
        Repr := Repr + {data};

      }
    }
  }

  method add(k: K,v: V)
    modifies  Repr
    requires valid()
    ensures valid()
    ensures fresh(Repr - old(Repr))
    ensures k in mapa && mapa[k] == Some(v)
  {

    if (size >= (data.Length * 3/4)) {
      resize();
    }

    remove(k);
    var b := bucket(k, data.Length);
    size := size + 1; //prof disse que size nao seria necessario para a prova
    assert forall k',v':: valid_data(k', v', mapa,data) && ((k' in mapa && mapa[k'] == Some(v')) <==> mem((k',v'), data[bucket(k', data.Length)]));
    assert forall i:: 0 <= i < data.Length ==> valid_hash(data,i) && forall k, v :: mem((k,v), data[i]) ==> bucket(k, data.Length) == i;

    Repr := Repr - {data};
    var old_list := data[b];

    data[b] := Cons((k,v), old_list);
    mapa := mapa[k := Some(v)];
    Repr := Repr + {data};

  }
}