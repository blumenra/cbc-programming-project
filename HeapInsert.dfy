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
	//alternation
	if heapsize == 0
	{
		a[heapsize]:=x;
	}
	else
	{
		a[heapsize]:=x;
		Heapify(a,heapsize,x);
	}		
	assert  hp(a[..], heapsize+1);
	assert multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x]);
	}


	method Heapify(a: array<int>,heapsize: nat, x: int)
	requires 0 < heapsize < a.Length
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
	ghost var old_seq:= a[..heapsize];
	ghost var old_seq2:= a[..heapsize+1];
    while (j > 0 && a[(j-1)/2] < a[j]) 
		invariant Inv(a,heapsize,x,j,old_seq,old_seq2);
		decreases j
   
    {
		var old1:=a[(j-1)/2];
		var old2:=a[j];
		var old_set:= multiset(a[..heapsize+1]);
		Swap(a, (j-1)/2, j,heapsize);
		assert  a[(j-1)/2]==old2;
		assert a[j]==old1;
		assert old_set==multiset(a[..heapsize+1]);
	  	j := (j-1)/2;
    }
	assert !(j > 0 && a[(j-1)/2] < a[j]);
	assert Inv(a,heapsize,x,j,old_seq,old_seq2);
	assert  hp(a[..], heapsize+1);
	assert multiset(a[..heapsize+1]) == multiset(old_seq2+[x]);
	
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


predicate Inv(a: array<int>,heapsize: nat, x: int , j:int ,old_seq:seq<int>,old_seq2:seq<int>)
reads a;
{
	0 <= j <= heapsize && 
	0 < heapsize < a.Length && 
	 hp(a[..], j) &&
	multiset(a[..j+1]) == multiset(a[..j]+[x]) &&
	multiset(a[..heapsize+1])==multiset(old_seq2) && 
	j>0 ==> AncestorIndex((j-1)/2,j) &&
	(forall k,h :: j < h <= k <= heapsize  && (k - 1) / 2 == j && j > 0 && AncestorIndex(h, k)  ==>  a[h] >= a[k])&&				
	a[j]==x &&
	multiset(a[..heapsize+1]) ==multiset(old_seq+[x])

}

