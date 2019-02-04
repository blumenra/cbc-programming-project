include "CCPR191-HeapSort-complete-30Dec18.dfy"

method HeapInsert(a: array<int>, heapsize: nat, x: int)
	requires heapsize < a.Length
	requires hp(a[..], heapsize)
	ensures hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	modifies a
	{
	assert heapsize < a.Length;
	assert hp(a[..], heapsize);
	a[heapsize]:=x;
	Heapify(a,heapsize,x);
	assert  hp(a[..], heapsize+1);
	assert multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x]);
	}


	method Heapify(a: array<int>,heapsize: nat, x: int)
	requires heapsize < a.Length
	requires  multiset(a[..heapsize+1]) == multiset(a[..heapsize]+[x])
	requires hp(a[..], heapsize)
	ensures hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	modifies a;
	{
	assert  heapsize < a.Length;
	assert multiset(a[..heapsize+1]) == multiset(a[..heapsize]+[x]);
	assert hp(a[..], heapsize);
    var j:=heapsize;
    while (j > 0 && a[(j-1)/2] < a[j]) 
		invariant 0 <= j <=heapsize
		invariant 	0 <= heapsize < a.Length
		invariant hp(a[..], j);
	    invariant multiset(a[..j+1]) == multiset(a[..j]+[x])
		invariant multiset(a[..heapsize+1])==multiset(old(a[..heapsize+1]))
		invariant   j>0 ==> AncestorIndex((j-1)/2,j) ;
		//invariant  ph(a[..],IndexSet(j+1,heapsize));
		invariant (forall k , h :: 0 < h <=k <= j  && k!=j && AncestorIndex(h, k)  ==> a[h] >= a[k])
		invariant	(forall k,h :: j < h <= k <= heapsize  && (k - 1) / 2 == j && j > 0 && AncestorIndex(h, k)  ==>  a[h] >= a[k]);					
		invariant a[j]==x ;
		invariant multiset(a[..heapsize+1]) ==multiset(old(a[..heapsize])+[x])
		decreases j
   
    {
		assert 0 <= j <=heapsize;
		assert 	0 <= heapsize < a.Length;
		assert hp(a[..], j);
		assert multiset(a[..j+1]) == multiset(a[..j]+[x]);
		assert multiset(a[..heapsize+1])==multiset(old(a[..heapsize+1]));
		assert   j>0 ==> AncestorIndex((j-1)/2,j) ;
	//	assert  ph(a[..],IndexSet(j+1,heapsize));
		assert (forall k , h :: 0 < h <=k <= j  && k!=j && AncestorIndex(h, k)  ==> a[h] >= a[k]);
		assert	(forall k,h :: j < h <= k <= heapsize  && (k - 1) / 2 == j && j > 0 && AncestorIndex(h, k)  ==>  a[h] >= a[k]);					
		assert a[j]==x ;
		assert multiset(a[..heapsize+1]) ==multiset(old(a[..heapsize])+[x]);

		var old1:=a[(j-1)/2];
		var old2:=a[j];
		var old_set:= multiset(a[..heapsize+1]);
		Swap(a, (j-1)/2, j,heapsize);
		assert a[(j-1)/2]==x;
		assert  a[(j-1)/2]==old2;
		assert a[j]==old1;
		assert old_set==multiset(a[..heapsize+1]);
	  	j := (j-1)/2;

		assert 0 <= j <=heapsize;
		assert 	0 <= heapsize < a.Length;
		assert hp(a[..], j);
		assert multiset(a[..j+1]) == multiset(a[..j]+[x]);
		assert multiset(a[..heapsize+1])==multiset(old(a[..heapsize+1]));
		assert   j>0 ==> AncestorIndex((j-1)/2,j) ;
		//assert  ph(a[..],IndexSet(j+1,heapsize));
		assert (forall k , h :: 0 < h <=k <= j  && k!=j && AncestorIndex(h, k)  ==> a[h] >= a[k]);
		assert	(forall k,h :: j < h <= k <= heapsize  && (k - 1) / 2 == j && j > 0 && AncestorIndex(h, k)  ==>  a[h] >= a[k]);					
		assert a[j]==x ;
		assert multiset(a[..heapsize+1]) ==multiset(old(a[..heapsize])+[x]);
	
    }
	assert  j>0 ==> AncestorIndex((j-1)/2,j) ;
	assert 0 <= j <=heapsize;
	assert 	0 <= heapsize < a.Length;
	assert hp(a[..], j);
	assert multiset(a[..j+1]) == multiset(a[..j]+[x]);
	assert multiset(a[..heapsize+1])==multiset(old(a[..heapsize+1]));
	assert   j>0 ==> AncestorIndex((j-1)/2,j) ;
	//assert  ph(a[..],IndexSet(j+1,heapsize));
	assert (forall k , h :: 0 < h <=k <= j  && k!=j && AncestorIndex(h, k)  ==> a[h] >= a[k]);
	assert	(forall k,h :: j < h <= k <= heapsize  && (k - 1) / 2 == j && j > 0 && AncestorIndex(h, k)  ==>  a[h] >= a[k]);					
	assert a[j]==x ;
	assert multiset(a[..heapsize+1]) ==multiset(old(a[..heapsize])+[x]);
	assert hp(a[..], heapsize+1);
	
	}


method Swap(a: array<int>, i: int, j: int,heapsize:nat)
  requires 0 <= i < j <= heapsize < a.Length
  requires  a[i] < a[j]
  ensures a[i] == old(a[j]);
  ensures a[j] == old(a[i]);
  ensures forall m :: heapsize < m < a.Length && m != i && m != j ==> a[m] == old(a[m]);
  ensures multiset(a[..heapsize+1]) == old(multiset(a[..heapsize+1]));
  modifies a;
{
  a[i], a[j] := a[j], a[i];
}


