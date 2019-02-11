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
	assert ph(a[..], IndexSet(0, heapsize));

	//alternation
	if Guard1(heapsize)
	{
		HeapInsert1(a,heapsize,x);
		
	}
	else
	{
		HeapInsert2(a,heapsize,x);
		
	}	
	assert ph(a[..], IndexSet(0,heapsize+1));	
	assert  hp(a[..], heapsize+1);
	assert multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x]);
	}

	predicate method Guard1(heapsize:nat)
{
	heapsize == 0
}

	method HeapInsert1(a: array<int>, heapsize: nat, x: int)
	requires Guard1(heapsize);
	requires heapsize < a.Length
	requires hp(a[..], heapsize)
	requires ph(a[..], IndexSet(0, heapsize))
	ensures a[heapsize]==x;
	ensures hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	ensures ph(a[..], IndexSet(0, heapsize+1))
	modifies a
	{
		Lemmax(a, heapsize, x);//assignemnt
		a[heapsize]:=x;
	}


	lemma Lemmax (a: array<int>, heapsize: nat, x: int)
	requires Guard1(heapsize);
	requires heapsize < a.Length
	requires hp(a[..], heapsize)
	requires ph(a[..], IndexSet(0, heapsize))
	ensures hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1][heapsize := x]) == multiset(old(a[..heapsize])+[x])
	ensures ph(a[..], IndexSet(0, heapsize+1))
	{
	}

	lemma Lemmax2 (a: array<int>, heapsize: nat, x: int)
	requires !Guard1(heapsize);
	requires heapsize < a.Length
	requires hp(a[..], heapsize)
	requires ph(a[..], IndexSet(0, heapsize))

	ensures 0 < heapsize < a.Length
	ensures multiset(a[..heapsize+1][heapsize := x]) == multiset(a[..heapsize]+[x])
	ensures hp(a[..], heapsize)
	ensures ph(a[..], IndexSet(0, heapsize))
	
	{
	}

	
	method HeapInsert2(a: array<int>, heapsize: nat, x: int)
	requires !Guard1(heapsize);
	requires heapsize < a.Length
	requires hp(a[..], heapsize)
	requires ph(a[..], IndexSet(0, heapsize))
	ensures hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	ensures ph(a[..], IndexSet(0, heapsize+1))
	modifies a
	{
		Lemmax2(a, heapsize, x);//assignemnt
		a[heapsize]:=x;
		Heapify(a,heapsize,x);
	}


	method Heapify(a: array<int>,heapsize: nat, x: int)
	requires 0 < heapsize < a.Length
	requires multiset(a[..heapsize+1]) == multiset(a[..heapsize]+[x])
	requires hp(a[..], heapsize)
	requires a[heapsize]==x
	requires ph(a[..], IndexSet(0, heapsize))

	ensures hp(a[..], heapsize+1)
	ensures ph(a[..], IndexSet(0, heapsize+1))
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	modifies a;
	{



	var j,old_j,old_seq,old_seq2,i:=Init_Heapify(a,heapsize, x);
	i,old_j,j:=Loop(j,old_j,old_seq,old_seq2,i,a,heapsize,x);
	

	assert Inv(a,heapsize,x,j,old_seq,old_seq2);


	assert !(j > 0 && a[(j-1)/2] < a[j]);
	assert j==0 ||  a[(j-1)/2] >= a[j];
	

	assert Inv(a,heapsize,x,j,old_seq,old_seq2);
	
	assert forall j:int ::
	0<=j<heapsize+1<=a.Length && (j == 0 || (j>0 && a[(j-1)/2] >= a[j])) && Inv(a,heapsize,x,j,old_seq,old_seq2) ==> 
	hp(a[..], j) && ph(a[..], IndexSet(0, j)) && ph(a[..], IndexSet(j, heapsize+1));


	assert ph(a[..], IndexSet(0, j)) && ph(a[..], IndexSet(j, heapsize+1));
	
	assert forall j:int ::
	0<=j<heapsize+1<=a.Length && (j == 0 || (j>0 && a[(j-1)/2] >= a[j])) && ph(a[..], IndexSet(0, j)) 
	&& ph(a[..], IndexSet(j, heapsize+1)) && Inv(a,heapsize,x,j,old_seq,old_seq2) 
	==> ph(a[..], IndexSet(0, heapsize+1)) && multiset(a[..heapsize+1]) == multiset(old_seq2+[x]);
	
	assert ph(a[..], IndexSet(0, heapsize+1));
	assert  hp(a[..], heapsize+1);
	assert multiset(a[..heapsize+1]) == multiset(old_seq2+[x]);
	
	}



method Loop(j0:nat,old_j0:nat,old_seq:seq<int>,old_seq2:seq<int>,i0:nat,a: array<int>,heapsize: nat, x: int) returns(i:nat,old_j:nat,j:nat)
requires j0==heapsize;
requires old_j0 == heapsize+1;
requires i0 == (j0-1)/2;
requires  0< j0 <= heapsize < a.Length;
requires Inv(a,heapsize,x,j0,old_seq,old_seq2);
ensures j<=j0 
ensures Inv(a,heapsize,x,j,old_seq,old_seq2) &&  (j==0 ||  a[(j-1)/2] >= a[j])
modifies a;
{

j:=j0;
old_j:=old_j0;
i:=i0;
assert j==heapsize;
assert old_j == heapsize+1;
assert i == (j-1)/2;
assert  0< j <= heapsize < a.Length;
assert Inv(a,heapsize,x,j,old_seq,old_seq2);

 while (j!=0 && a[(j-1)/2] < a[j])
		invariant Inv(a,heapsize,x,j,old_seq,old_seq2);
		decreases j
   
    {
		
		assert Inv(a,heapsize,x,j,old_seq,old_seq2);
		
		assert forall j:int ::
		0<=j<heapsize+1<=a.Length && (j > 0 && a[(j-1)/2] < a[j]) && Inv(a,heapsize,x,j,old_seq,old_seq2) ==> 
		hp(a[..], j) && ph(a[..], IndexSet(0, j)) && ph(a[..], IndexSet(j, heapsize+1));

		assert 0 < j <= heapsize && 0 < heapsize < a.Length && hp(a[..], j) && ph(a[..], IndexSet(0, j)) && ph(a[..], IndexSet(j, heapsize+1));
				 
		var old1:=a[(j-1)/2]; 
		var old2:=a[j];
		var old_set:= multiset(a[..heapsize+1]);
		
		  i := (j-1)/2;
		
		assert ph(a[..], IndexSet(0, j));
		assert ph(a[..], IndexSet(j+1, heapsize+1));
		assert ph(a[..], IndexSet(0, i));


		assert ph(a[..], IndexSet(0, j));
		assert j <= heapsize;
		assert j == (old_j-1)/2 || (j == heapsize && old_j == heapsize+1);
		

		assert j<=heapsize;

	
		
		assert ph(a[..], IndexSet(0, j));
		assert ph(a[..], IndexSet(j, heapsize+1));
		assert ph(a[..], IndexSet(j, old_j));
		
		Swap(a, i, j,heapsize);
	
		assert ph(a[..], IndexSet(0, i));
		assert ph(a[..], IndexSet(i+1, heapsize+1));
		assert ph(a[..], IndexSet(i, j));

		assert  a[i]==old2;
		assert a[j]==old1;
		assert old_set == multiset(a[..heapsize+1]);
	

		  old_j := j;
	  	   j := i;

		
		assert j == (old_j-1)/2;
		
		assert Inv(a,heapsize,x,j,old_seq,old_seq2);
		assert ph(a[..], IndexSet(0, j)) && ph(a[..], IndexSet(j, heapsize+1));

	}
	assert Inv(a,heapsize,x,j,old_seq,old_seq2) &&  (j==0 ||  a[(j-1)/2] >= a[j]);
	
}


method  Init_Heapify(a: array<int>,heapsize: nat, x: int) returns (j:nat,old_j:nat,old_seq:seq<int>,old_seq2:seq<int>,i:nat)
requires 0 < heapsize < a.Length
	requires multiset(a[..heapsize+1]) == multiset(a[..heapsize]+[x])
	requires hp(a[..], heapsize)
	requires a[heapsize]==x
	requires ph(a[..], IndexSet(0, heapsize))
	ensures j==heapsize;
	ensures old_j == heapsize+1;
	ensures i == (j-1)/2;
	ensures 0<j<=heapsize<a.Length;

	ensures Inv(a,heapsize,x,j,old_seq,old_seq2);
{
	assert  0 < heapsize < a.Length;
	assert multiset(a[..heapsize+1]) == multiset(a[..heapsize]+[x]);
	assert hp(a[..], heapsize);
	assert a[heapsize]==x;
	assert ph(a[..], IndexSet(0, heapsize));
	
	assert ph(a[..], IndexSet(heapsize+1, heapsize+1));

     j:=heapsize;

	assert ph(a[..], IndexSet(j+1, heapsize+1));
  
	  old_j := heapsize+1;
	assert old_j >= j;

	 old_seq:= a[..heapsize];
	 old_seq2:= a[..heapsize+1];

	assert ph(a[..], IndexSet(0, j));
	assert ph(a[..], IndexSet(j, heapsize+1));
	assert ph(a[..], IndexSet(j, old_j));

	 i := (j-1)/2;
	assert j == heapsize;
	assert j == heapsize && old_j == heapsize+1;
}


method Swap(a: array<int>,  i: int, j: nat,heapsize:nat)
  requires 0 <= i < j <= heapsize < a.Length
  requires  a[i] < a[j]
  requires ph(a[..], IndexSet(0, i))
  requires ph(a[..], IndexSet(0, j))
  requires ph(a[..], IndexSet(j+1, heapsize+1))

  ensures a[i] == old(a[j]);
  ensures a[j] == old(a[i]);
  ensures forall m :: heapsize < m < a.Length && m != i && m != j ==> a[m] == old(a[m]);
  ensures a[..i] == old(a[..i])
  ensures ph(a[..], IndexSet(0, i))
  ensures a[i+1..j] == old(a[i+1..j])
  ensures ph(a[..], IndexSet(i, j))
  ensures a[j+1..] == old(a[j+1..])
  ensures ph(a[..], IndexSet(j+1, heapsize+1))
  ensures multiset(a[..heapsize+1]) == old(multiset(a[..heapsize+1]));
  modifies a;
{
  a[i], a[j] := a[j], a[i];
}



predicate Inv(a: array<int>,heapsize: nat, x: int , j:nat , old_seq:seq<int>,old_seq2:seq<int>)
reads a;
{
	
	0 < j <= heapsize && 
	0 < heapsize < a.Length &&
	hp(a[..], j) && 
	
	ph(a[..], IndexSet(0, j))&&
	ph(a[..], IndexSet(j, heapsize+1)) &&
	
	multiset(a[..j+1]) == multiset(a[..j]+[x]) &&
	multiset(a[..heapsize+1]) == multiset(old_seq2) && 
	j>0 ==> AncestorIndex((j-1)/2,j) &&
	(forall k,h :: j < h <= k <= heapsize  && (k - 1) / 2 == j && j > 0 && AncestorIndex(h, k)  ==>  a[h] >= a[k])&&				
	a[j]==x &&
	multiset(a[..heapsize+1]) == multiset(old_seq+[x])

}
