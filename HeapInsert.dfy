
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

	a[heapsize] := x;
	
	Heapify(a,heapsize,x);

	assert  hp(a[..], heapsize+1);
	assert multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x]);
}


method Heapify(a: array<int>,heapsize: nat, x: int)
	requires heapsize < a.Length
	requires a[heapsize]==x
	requires hp(a[..], heapsize)
	requires ph(a[..], IndexSet(0, heapsize))
	requires multiset(a[..heapsize+1]) == multiset(a[..heapsize]+[x])
	ensures hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1]) == multiset(old(a[..heapsize])+[x])
	modifies a
{

	assert ph(a[..], IndexSet(heapsize+1, heapsize+1));
	assert ph(a[..], IndexSet(0, heapsize));
	assert ph(a[..], IndexSet(heapsize, heapsize+1));
	assert Inv(a,heapsize,x,heapsize,a[..heapsize],a[..heapsize]+[x]);
		
	
	var  old_seq, old_seq2 := a[..heapsize], a[..heapsize+1];// introduce local variable
	var j:nat := heapsize;// introduce local variable

	assert ph(a[..], IndexSet(j+1, heapsize+1));
	assert ph(a[..], IndexSet(0, j));
	assert ph(a[..], IndexSet(j, heapsize+1));
	assert Inv(a,heapsize,x,j,old_seq,old_seq2);

	j := Loop(j,old_seq,old_seq2,a,heapsize,x);

	assert  hp(a[..], heapsize+1);
	assert multiset(a[..heapsize+1]) == multiset(old_seq+[x]);
}




method Loop(j0:nat,old_seq:seq<int>,old_seq2:seq<int>,a: array<int>,heapsize: nat, x: int) returns(j:nat)
	requires j0 == heapsize < a.Length
	requires Inv(a,heapsize,x,j0,old_seq,old_seq2)
	ensures  Inv(a,heapsize,x,j,old_seq,old_seq2) && !(j!=0 && a[parent(j)] < a[j])
	ensures  hp(a[..], heapsize+1);
	ensures multiset(a[..heapsize+1]) == multiset(old_seq+[x]);
	modifies a
{//contract frame
	j := j0;

	assert j==heapsize;
	assert Inv(a,heapsize,x,j,old_seq,old_seq2);
	assert j==j0;
	// iteration
	while (j!=0 && a[parent(j)] < a[j])
		invariant Inv(a,heapsize,x,j,old_seq,old_seq2) 
		decreases j
	{
		j := Loop_Body(j,old_seq,old_seq2,a,heapsize,x);
	}

	assert Inv(a,heapsize,x,j,old_seq,old_seq2);
	assert j ==0 || a[parent(j)] >= a[j]; // NOT of while guard
			
	Lemma_end_loop(a,heapsize,x,j,old_seq,old_seq2);
	
	assert  hp(a[..], heapsize+1);
	assert multiset(a[..heapsize+1]) == multiset(old_seq+[x]);
}

method Loop_Body(j0:nat,old_seq:seq<int>,old_seq2:seq<int>,a: array<int>,heapsize: nat, x: int) returns(j:nat)
	requires Inv(a,heapsize,x,j0,old_seq,old_seq2)
	requires j0!=0 && a[(j0-1)/2] < a[j0]
	ensures Inv(a,heapsize,x,j,old_seq,old_seq2)
	ensures j0 > j >= 0
	modifies a
{//contract frame 
	assert Inv(a,heapsize,x,j0,old_seq,old_seq2);
	j:=j0; 

	assert Inv(a,heapsize,x,j,old_seq,old_seq2) ==> (0 < j <= heapsize < a.Length);
	assert Inv(a,heapsize,x,j,old_seq,old_seq2) ==> ph(a[..], IndexSet(0, j)) && ph(a[..], IndexSet(j, heapsize+1));

	Swap(a, parent(j), j,heapsize,x,old_seq,old_seq2);

	assert Inv(a,heapsize,x,parent(j),old_seq,old_seq2);

	j := parent(j);
		
	assert Inv(a,heapsize,x,j,old_seq,old_seq2);
}


lemma Lemma_end_loop(a: array<int>,heapsize: nat, x: int , j:nat , old_seq:seq<int>,old_seq2:seq<int>)
	requires Inv(a,heapsize,x,j,old_seq,old_seq2)
	requires j==0 || a[parent(j)] >= a[j]
	requires ph(a[..], IndexSet(0, j)) && ph(a[..], IndexSet(j, heapsize+1)) && ph(a[..], IndexSet(0, heapsize+1)-{j}) 
	ensures  hp(a[..], heapsize+1)
	ensures multiset(a[..heapsize+1]) == multiset(old_seq+[x]);
{	
	//alternation
	if(j == 0)
	{
		assert j == 0;
		//==>
		assert ph(a[..], IndexSet(0, heapsize+1)); // by pre condition
		//==>
		assert hp(a[..], heapsize+1);
		assert multiset(a[..heapsize+1]) == multiset(old_seq+[x]) by { assert Inv(a,heapsize,x,j,old_seq,old_seq2); /* pre cond. */}
	}
	else
	{
		assert ph(a[..], IndexSet(0, j)); // pre condition
		//==>
		assert hp(a[..], j);

		assert a[parent(j)] >= a[j]; // pre condition (else part)
		//==>		
		assert hp(a[..], j+1) by { Lemma_end_loop1(a, j); }
		assert multiset(a[..heapsize+1]) == multiset(old_seq+[x]) by { assert Inv(a,heapsize,x,j,old_seq,old_seq2); /* pre cond. */}
	}

	assert hp(a[..], heapsize+1);
	assert multiset(a[..heapsize+1]) == multiset(old_seq+[x]);
}

function method parent(j: nat): nat
	requires 0 < j 
{
	(j-1)/2
}

function IndexAncestorsSet(start: nat, end: nat, j: nat): set<nat>
{
	set i: nat | i < end && InRange(start, i, end) && AncestorIndex(i, j)
}

lemma Lemma_end_loop1(a: array<int>, heapsize: nat)
	requires 0 < heapsize < a.Length
	requires hp(a[..], heapsize)
	requires a[parent(heapsize)] >= a[heapsize];
	ensures hp(a[..], heapsize+1)
{
	assert hp(a[..], heapsize);
	//<==>
	assert forall i,j :: 0 <= i < heapsize && 0 <= j < heapsize && AncestorIndex(i, j) ==> a[..][i] >= a[..][j];
	assert a[parent(heapsize)] >= a[heapsize];
	//==>
	assert hp(a[..], parent(heapsize));
	//==>
	assert forall i :: 0 <= i < heapsize && AncestorIndex(i, parent(heapsize)) ==> a[..][i] >= a[..][parent(heapsize)];
	assert a[parent(heapsize)] >= a[heapsize];
	//==>
	ghost var s1 := IndexAncestorsSet(0, heapsize+1, parent(heapsize));
	ghost var s2 := IndexAncestorsSet(0, heapsize+1, heapsize);

	assert forall i:: i in s1 ==> a[i] >= a[parent(heapsize)];

	L2(heapsize);

	assert s2 == s1 + {heapsize};
	//==>
	assert forall i:: i in s2 ==> a[i] >= a[heapsize];

	assert forall i :: 0 <= i < heapsize && AncestorIndex(i, heapsize) ==> a[..][i] >= a[..][heapsize];
	//==>
	assert forall i,j :: 0 <= i < heapsize && 0 <= j <= heapsize && AncestorIndex(i, j) ==> a[..][i] >= a[..][j];
	//==>
	assert forall i,j :: 0 <= i <= heapsize && 0 <= j <= heapsize && AncestorIndex(i, j) ==> a[..][i] >= a[..][j];
	//<==>
	assert hp(a[..], heapsize+1);
}

lemma L2(j: nat)
	requires 0 < j
	ensures IndexAncestorsSet(0, j+1, j) == IndexAncestorsSet(0, j+1, parent(j)) + {j}
{
	calc
	{
		IndexAncestorsSet(0, j+1, j);
	== 
		IndexAncestorsSet(0, parent(j)+1, j) + IndexAncestorsSet(parent(j)+1, j+1, j);
	== { L3(j); }
		IndexAncestorsSet(0, parent(j)+1, parent(j)) + IndexAncestorsSet(parent(j)+1, j+1, j);
	==
		IndexAncestorsSet(0, j+1, parent(j)) + IndexAncestorsSet(parent(j)+1, j+1, j);
	== 
		IndexAncestorsSet(0, j+1, parent(j)) + {j};
	}
}

lemma L3(j: nat)
	requires 0 < j
	ensures IndexAncestorsSet(0, parent(j)+1, j) == IndexAncestorsSet(0, parent(j)+1, parent(j))
{
	var s1 := IndexAncestorsSet(0, parent(j)+1, j);
	var s2 := IndexAncestorsSet(0, parent(j)+1, parent(j));
	
	assert s1 <= s2 by { L4(j); }
	assert s1 >= s2 by { L5(j); }
	//==>
	assert s1 ==s2;
	//==>
	assert IndexAncestorsSet(0, parent(j)+1, j) == IndexAncestorsSet(0, parent(j)+1, parent(j));
}

lemma L4(j: nat)
	requires 0 < j
	ensures IndexAncestorsSet(0, parent(j)+1, j) <= IndexAncestorsSet(0, parent(j)+1, parent(j))
{
	forall i | 0 <= i < j && AncestorIndex(i, j) ensures AncestorIndex(i, parent(j)) {
		L4step(i, j);
	}
	//==>
	assert forall i :: 0 <= i < j && AncestorIndex(i, j) ==> AncestorIndex(i, parent(j));
	//==>
	assert IndexAncestorsSet(0, parent(j)+1, j) <= IndexAncestorsSet(0, parent(j)+1, parent(j));
}

lemma L4step(i: nat, j: nat)
	requires 0 <= i < j
	requires AncestorIndex(i, j)
	ensures AncestorIndex(i, parent(j))
	decreases j-i
{
	assert AncestorIndex(i, j);
	//<==> def.
	assert i == j || (j > 2*i && ((AncestorIndex(2*i+1, j) || AncestorIndex(2*i+2, j))));
	//==>
	if(i == j)//alternation
	{
		assert AncestorIndex(j, j);
		//==>
		assert AncestorIndex(j, parent(j)) by { assert parent(j) < j; }
		//==>
		assert AncestorIndex(i, parent(j));
	}
	else
	{
		assert j > 2*i && ((AncestorIndex(2*i+1, j) || AncestorIndex(2*i+2, j)));
		
		if AncestorIndex(2*i+1, j)//alternation
		{
			assert parent(2*i+1) == i;
			//==> 2*i+1 is a child of i
			//==> i is at least grand parent of j
			assert AncestorIndex(i, parent(j));
		}
		else
		{
			assert AncestorIndex(2*i+2, j);
			assert parent(2*i+2) == i;
			//==> 2*i+2 is a child of i
			//==> i is at least grand parent of j
			assert AncestorIndex(i, parent(j));
		}
		
		assert AncestorIndex(i, parent(j));
	}

	assert AncestorIndex(i, parent(j));
}

lemma L5(j: nat)
	requires 0 < j
	ensures IndexAncestorsSet(0, parent(j)+1, j) >= IndexAncestorsSet(0, parent(j)+1, parent(j))
{
	forall i | 0 <= i < j && AncestorIndex(i, parent(j)) ensures AncestorIndex(i, j) {
		L5step(i, j);
	}
	//==>
	assert forall i:: 0 <= i < j && AncestorIndex(i, parent(j)) ==> AncestorIndex(i, j);
	//==>
	assert IndexAncestorsSet(0, parent(j)+1, j) >= IndexAncestorsSet(0, parent(j)+1, parent(j));
}

lemma L5step(i: nat, j: nat)
	requires 0 <= i < j
	requires AncestorIndex(i, parent(j))
	ensures AncestorIndex(i, j)
	decreases j-i
{
	assert AncestorIndex(i, parent(j));
	//<==> def.
	assert i == parent(j) || (parent(j) > 2*i && ((AncestorIndex(2*i+1, parent(j)) || AncestorIndex(2*i+2, parent(j)))));
	//==>
	if(i == parent(j))//alternation
	{
		assert AncestorIndex(parent(j), j);
		//==>
		assert AncestorIndex(i, j);
	}
	else
	{
		assert parent(j) > 2*i && ((AncestorIndex(2*i+1, parent(j)) || AncestorIndex(2*i+2, parent(j))));
		
		if AncestorIndex(2*i+1, parent(j))//alternation
		{
			assert parent(2*i+1) == i;
			//==> 2*i+1 is a child of i
			assert AncestorIndex(i, j);
		}
		else
		{
			assert AncestorIndex(2*i+2, parent(j));
			assert parent(2*i+2) == i;
			//==> 2*i+2 is a child of i
			assert AncestorIndex(i, j);
		}
		
		assert AncestorIndex(i, j);
	}

	assert AncestorIndex(i, j);
}

method Swap(a: array<int>, i: int, j: nat,heapsize:nat, x:int,old_seq:seq<int>,old_seq2:seq<int>)
	requires 0 <= i < j <= heapsize < a.Length && heapsize == |old_seq| && |old_seq2|==heapsize+1
	requires i == parent(j)
	requires  a[i] < a[j] == x
	requires Inv(a,heapsize,x,j,old_seq,old_seq2)

	ensures x == a[i] > a[j]
	ensures Inv(a,heapsize,x,i,old_seq,old_seq2)
	modifies a
{
	SwapProof(a,i,j,heapsize,x,old_seq,old_seq2);

	a[i], a[j] := a[j], a[i];

	assert  SemiHeapPred(a,heapsize,i);
	InvProof(a,i,j,heapsize,x,old_seq,old_seq2);		
	//==>
	assert Inv(a,heapsize,x,i,old_seq,old_seq2);
}

lemma SwapProof(a: array<int>, i: int, j: nat,heapsize:nat, x:int,old_seq:seq<int>,old_seq2:seq<int>)
	requires 0 <= i < j <= heapsize < a.Length && i == parent(j)
	requires IntegPred(a,heapsize,j,x,old_seq,old_seq2)
	requires a[i] < a[j]==x
	requires SemiHeapPred(a,heapsize,j)
	ensures var q := a[..][i := a[j]][j := a[i]];  
		&& ph(q[..], IndexSet(0, i))
		&& ph(q[..], IndexSet(i, heapsize+1))
		&& ph(q[..], IndexSet(0, heapsize+1) - {i})
		&& q[..i]==a[..i] && q[i]==x
		&& multiset(q[..i+1]) == multiset(a[..i]+[x]) 
		&& multiset(q[..heapsize+1]) == multiset(old_seq2) == multiset(old_seq+[x]) 
		&& multiset(q[..heapsize+1]) == multiset(q[..heapsize+1]) 

{
	var q := a[..][i := a[j]][j := a[i]];

	assert ph(q[..], IndexSet(0, i)) by { LemmaMaxLowerHeap(a,i,j,heapsize,x,old_seq,old_seq2);}
	assert ph(q[..], IndexSet(i, heapsize+1)) by { LemmaMaxUpperHeap(a,i,j,heapsize,x,old_seq,old_seq2); }
	assert multiset(a[..heapsize+1]) == multiset(q[..heapsize+1]) by { LemmaSwapMaintainsMultiset(a[..],q[..],i,j); }
	assert ph(q[..], IndexSet(0, heapsize+1) - {i}) by{ LemmaPhWithoutI(a,i,j,heapsize,x,old_seq,old_seq2); }
}

lemma LemmaPhWithoutI(a: array<int>, i: int, j: nat,heapsize:nat, x:int,old_seq:seq<int>,old_seq2:seq<int>)
	requires 0 <= i < j <= heapsize < a.Length && i == parent(j)
	requires IntegPred(a,heapsize,j,x,old_seq,old_seq2)
	requires a[i] < a[j] == x
	requires SemiHeapPred(a,heapsize,j)
	ensures var q := a[..][i := a[j]][j := a[i]]; ph(q[..], IndexSet(0, heapsize+1) - {i}) 
{	
	var q := a[..][parent(j) := a[j]][j := a[parent(j)]];			
			
	forall m | m in  IndexSet(0, heapsize+1) && AncestorIndex(m,j) ensures q[m]>=q[j] {
		// Pre conds.
		assert 0 < j <= heapsize < a.Length;
		assert a[parent(j)] < a[j];
		assert SemiHeapPred(a,heapsize,j);

		// above assignment
		assert q == a[..][parent(j) := a[j]][j := a[parent(j)]];

		// forall condition
		assert m in  IndexSet(0, heapsize+1) && AncestorIndex(m,j);

		//==>
		LemmaPhWithoutIstep(a, j, heapsize, m, q);
	}
	//==>
	assert forall m :: m in  IndexSet(0, heapsize+1) && AncestorIndex(m,j) ==> q[m]>=q[j];
	//==>
	assert forall l,k:: l in  IndexSet(0, heapsize+1) && k in  IndexSet(0, heapsize+1) && AncestorIndex(l,k) && l!=i && k!=i ==>  q[l] >= q[k];
	assert (forall l,k:: l in  IndexSet(0, heapsize+1) && k in  IndexSet(0, heapsize+1) && AncestorIndex(l,k) && l!=i && k!=i ==>  q[l] >= q[k])==> ph(q[..], IndexSet(0, heapsize+1) - {i});
	//==>
	assert var q := a[..][i := a[j]][j := a[i]]; ph(q[..], IndexSet(0, heapsize+1) - {i});
}

lemma LemmaPhWithoutIstep(a: array<int>, j: nat,heapsize:nat, m:nat, q:seq<int>)
	requires 0 < j <= heapsize < a.Length
	requires a[parent(j)] < a[j]
	requires m in  IndexSet(0, heapsize+1) && AncestorIndex(m,j)
	requires q == a[..][parent(j) := a[j]][j := a[parent(j)]]
	requires SemiHeapPred(a,heapsize,j);
	ensures q[m]>=q[j]
{
	assert AncestorIndex(m,j);
	//==>
	if(m == j)//alternation
	{
		// Trivial
		assert q[m]>=q[j];
	}
	else // m is at least the parent of j
	{
		assert ph(a[..], IndexSet(0, j)) by { assert SemiHeapPred(a,heapsize,j); /* pre cond. */}
		assert a[parent(j)] < a[j]; // pre cond.
		//==>
		assert q[parent(j)] >= q[j]; // swapped
		
		assert AncestorIndex(parent(j), j);
		//==>

		assert AncestorIndex(m, parent(j)) by { L4step(m, j); }
		//==>
		assert q[m]>=q[j];
	}
	assert q[m]>=q[j];
}

lemma LemmaMaxLowerHeap(a: array<int>, i: int, j: nat,heapsize:nat, x:int,old_seq:seq<int>,old_seq2:seq<int>)
	requires 0 <= i < j <= heapsize < a.Length  
	requires i == parent(j)
	requires  a[i] < a[j]
	requires ph(a[..], IndexSet(0, j))
	ensures var q := a[..][i := a[j]][j := a[i]]; ph(q[..], IndexSet(0, i))
{
	var q := a[..][i := a[j]][j := a[i]]; 
	assert ph(q[..], IndexSet(0, i));
}

lemma LemmaMaxUpperHeap(a: array<int>, i: int, j: nat,heapsize:nat, x:int,old_seq:seq<int>,old_seq2:seq<int>)
	requires 0 <= i < j <= heapsize < a.Length  
	requires i == parent(j)
	requires a[i] < a[j]
	requires ph(a[..], IndexSet(0, j))
	requires ph(a[..], IndexSet(j, heapsize+1))
	requires ph(a[..], IndexSet(0, heapsize+1) - {j})
	ensures var q := a[..][i := a[j]][j := a[i]]; 
		&& ph(q[..], IndexSet(i, heapsize+1)) 
{ 
	var q := a[..][i := a[j]][j := a[i]]; 
	assert ph(q[..], IndexSet(i, heapsize+1));
}

lemma InvProof(a: array<int>, i: nat, j: nat,heapsize:nat, x:int,old_seq:seq<int>,old_seq2:seq<int>)
	requires 0 <= i < j <= heapsize < a.Length &&  i == parent(j) 
	requires|old_seq|==|a[..heapsize]| && |old_seq2|==heapsize+1
	requires SemiHeapPred(a,heapsize,i)
	requires x == a[i] > a[j]
	requires  multiset(a[..heapsize+1]) == multiset(old_seq2)
	requires a[i]==x
		&& multiset(a[..i+1]) == multiset(a[..i]+[x]) 
		&& multiset(a[..heapsize+1]) == multiset(old_seq2) == multiset(old_seq+[x]) 
		&& multiset(a[..heapsize+1]) == multiset(a[..heapsize+1]) 
	requires hp(old_seq2,heapsize)
	ensures Inv(a,heapsize,x,i,old_seq,old_seq2)
{
	assert IntegPred(a,heapsize,i,x,old_seq,old_seq2) ;
}

predicate Inv(a: array<int>,heapsize: nat, x: int , j:nat , old_seq:seq<int>,old_seq2:seq<int>)
	reads a
{
	j <= heapsize < a.Length &&
	a[j] == x &&

	SemiHeapPred(a,heapsize,j) &&
	IntegPred(a,heapsize,j,x,old_seq,old_seq2) &&
	BigJPred(a, heapsize, j, x, old_seq) && 
		
	|old_seq|==|a[..heapsize]| &&
	|old_seq2|==heapsize+1 && 
	hp(old_seq2,heapsize)
}

predicate BigJPred(a:array<int>, heapsize:nat, j:nat, x:int, old_seq:seq<int>)
	reads a	
{
	j>0 ==>	AncestorIndex(parent(j),j) &&

	forall i, h ::
		0 <= i < parent(j) == j < h <= heapsize && 
		AncestorIndex(h, heapsize) && 
		AncestorIndex(i, j-1) 
	==> 
		a[h] >= a[heapsize]  &&  a[i] >= a[j-1]
}
	
predicate SemiHeapPred(a:array<int>, heapsize:nat, j:nat)
	reads a
{
	j <= heapsize < a.Length && 
	ph(a[..], IndexSet(0, j))&& ph(a[..], IndexSet(j, heapsize+1)) &&  
	ph(a[..], IndexSet(0, heapsize+1)-{j})
}
	
predicate IntegPred(a:array<int>, heapsize:nat, j:nat, x:int, old_seq:seq<int>, old_seq2:seq<int>)
	reads a
{
	j <= heapsize < a.Length &&
	multiset(a[..j+1]) == multiset(a[..j]+[x]) &&
	multiset(a[..heapsize+1]) == multiset(old_seq2) == multiset(old_seq+[x]) 
}
