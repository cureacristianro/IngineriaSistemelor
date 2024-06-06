predicate isSorted(a:array<int>)
  reads a
{
  forall i:nat, j:nat :: i <= j < a.Length ==> a[i] <= a[j]
}

// a[lo] <= a[lo+1] <= ... <= a[hi-2] <= a[hi-1]  
method binSearch(a:array<int>, K:int) returns (b:bool)
  requires isSorted(a)
  ensures b == exists i:nat :: i < a.Length && a[i] == K
{
	var lo: nat := 0 ;
	var hi: nat := a.Length ;
	while (lo < hi)
    decreases hi - lo
    invariant  0 <= lo <= hi <= a.Length
    //invariant forall j:nat :: j < lo ==> a[j] < K
    invariant forall i:nat :: (i < lo || hi <= i < a.Length) ==> a[i] != K
	{
		var mid: nat := (lo + hi) / 2 ;   assert  lo <= mid <= hi ;
		if (a[mid] < K) {                 assert  a[lo] <= a[mid]; 
                                      assert  a[mid] < K ;
			lo := mid + 1 ;                 assert              mid < lo <= hi;
		} else if (a[mid] > K) {          assert  K < a[mid];
			hi := mid ;                     assert              lo <= hi == mid;
		} else {
			return true ;                   assert a[mid] == K;
		}
	}
	return false ;                     
}

