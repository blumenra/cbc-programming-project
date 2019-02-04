predicate Sorted(a: array<int>)
	reads a
{
	forall i,j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}

predicate SortedSequence(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

method MergeSort(a: array<int>) returns (b: array<int>)
	ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
	decreases a.Length
{
b := new int[a.Length];
	if(a.Length <= 1){
		b := a;
	}
	else{
		
		var mid := a.Length/2;

		var leftSeq := a[0..mid];
		var rightSeq := a[mid..(a.Length)];
		var leftArr := new int[|leftSeq|];
		var rightArr := new int[|rightSeq|];

		var i:nat := 0;

		while(i < leftArr.Length)
		invariant forall k:: 0 <= k < i <= leftArr.Length ==> leftArr[k] == leftSeq[k]
		invariant 0 <= i <= leftArr.Length
		{

			leftArr[i] := leftSeq[i];
			i := i+1;
		}
		
		assert i == leftArr.Length;
		assert forall k:: 0 <= k < i <= leftArr.Length ==> leftArr[k] == leftSeq[k];
		//==>
		assert forall k:: 0 <= k  < leftArr.Length ==> leftArr[k] == leftSeq[k];
		//==>
		assert leftArr[..] == leftSeq;

		var j:nat := 0;
		while(j < rightArr.Length)
		invariant forall k:: 0 <= k < j <= rightArr.Length ==> rightArr[k] == rightSeq[k]
		invariant leftArr[..] == leftSeq
		invariant 0 <= j <= rightArr.Length
		{

			rightArr[j] := rightSeq[j];

			j := j+1;
		}
		
		assert forall k:: 0 <= k < j <= rightArr.Length ==> rightArr[k] == rightSeq[k];
		assert j == rightArr.Length;

		//==>
		
		assert leftArr[..] == leftSeq;
		assert rightArr[..] == rightSeq;
		
		//==>
		assert forall k:: 0 <= k < leftArr.Length ==> leftArr[k] == a[k];


		//==>
		assert forall k:: 0 <= k < mid ==> leftArr[k] == a[k];
		assert forall i:: 0 <= i < |rightArr[..]| ==> rightArr[..][i] == rightSeq[i];

		//==>
		assert forall i:: 0 <= i < leftArr.Length ==> leftArr[i] == a[i];
		assert forall i:: 0 <= i < |rightArr[..]| ==> rightArr[..][i] == a[mid..a.Length][i];

		//==>
		mulset2(leftArr[..], a[0..mid]);
		mulset2(rightArr[..], a[mid..a.Length]);
		
		assert multiset(leftArr[..]) == multiset(a[0..mid]);
		assert multiset(rightArr[..]) == multiset(a[mid..a.Length]);

		mulset(a);
		assert multiset(a[..]) == multiset(a[0..mid])+multiset(a[mid..a.Length]);
		// ==>

		assert multiset(a[..]) == multiset(leftArr[..])+multiset(rightArr[..]);
		
		var leftSortedArr := MergeSort(leftArr);
		
		




		assert multiset(a[..]) == multiset(leftArr[..])+multiset(rightArr[..]);
		
		var rightSortedArr := MergeSort(rightArr);

		Merge(b, leftSortedArr, rightSortedArr);
		
		assert Sorted(b) && multiset(b[..]) == multiset(leftSortedArr[..])+multiset(rightSortedArr[..]);
		//==>
		assert multiset(a[..]) == multiset(leftSortedArr[..])+multiset(rightSortedArr[..]);
		//==>
		assert multiset(a[..]) == multiset(b[..]);
	}


	assert multiset(a[..]) == multiset(b[..]);
}

method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
{
	var bi:nat := 0;
	var ci:nat := 0;
	var di:nat := 0;
	
	while(ci < c.Length && di < d.Length)
		invariant 0 <= bi <= b.Length && 0 <= ci <= c.Length && 0 <= di <= d.Length
		invariant bi == ci+di
		invariant SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
		invariant SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
		invariant forall k:: 0 <= k < ci ==> c[k] in b[0..bi]
		invariant forall k:: 0 <= k < di ==> d[k] in b[0..bi]
		invariant forall ck:: 0 <= ck < ci ==> b[bi-1] >= c[ck]
		invariant bi >= di && bi >= ci
		invariant if di < d.Length then forall k:: 0 <= k < bi ==> b[k] <= d[di] else true
		invariant if ci < c.Length then forall k:: 0 <= k < bi ==> b[k] <= c[ci] else true
		invariant multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di])

		decreases c.Length-ci
		decreases d.Length-di
	{

		if(c[ci] <= d[di]){
			assert forall k:: 0 <= k < di ==> d[k] in b[0..bi];

			b[bi] := c[ci];
			
			assert forall k:: 0 <= k < di ==> d[k] in b[0..bi];
			L(b[..], bi, c[..], ci);
			//==>
			assert forall k:: 0 <= k < ci+1 ==> c[k] in b[0..bi+1];
			assert forall k:: 0 <= k < di ==> d[k] in b[0..bi+1];
			assert multiset(b[..bi+1]) == multiset(c[..ci+1]) + multiset(d[..di]);

			ci := ci+1;
			
			assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi+1];
			assert forall k:: 0 <= k < di ==> d[k] in b[0..bi+1];
			assert multiset(b[..bi+1]) == multiset(c[..ci]) + multiset(d[..di]);
		}
		else{
			
			assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi];
			b[bi] := d[di];
			
			assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi];
			L(b[..], bi, d[..], di);
			//==>
			assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi+1];
			assert forall k:: 0 <= k < di+1 ==> d[k] in b[0..bi+1];
			di := di+1;
			
			assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi+1];
			assert forall k:: 0 <= k < di ==> d[k] in b[0..bi+1];
			assert multiset(b[..bi+1]) == multiset(c[..ci]) + multiset(d[..di]);
		}

		assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi+1];
		assert forall k:: 0 <= k < di ==> d[k] in b[0..bi+1];
		assert multiset(b[..bi+1]) == multiset(c[..ci]) + multiset(d[..di]);

		bi := bi+1;

		assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi];
		assert forall k:: 0 <= k < di ==> d[k] in b[0..bi];
		assert multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di]);
	}

	while(ci < c.Length)
		invariant 0 <= bi <= b.Length && 0 <= ci <= c.Length && 0 <= di <= d.Length
		invariant bi == ci+di
		invariant SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
		invariant SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
		invariant forall k:: 0 <= k < ci ==> c[k] in b[0..bi]
		invariant forall k:: 0 <= k < di ==> d[k] in b[0..bi]
		invariant forall ck:: 0 <= ck < ci ==> b[bi-1] >= c[ck]
		invariant bi >= di && bi >= ci
		invariant if di < d.Length then forall k:: 0 <= k < bi ==> b[k] <= d[di] else true
		invariant if ci < c.Length then forall k:: 0 <= k < bi ==> b[k] <= c[ci] else true
		invariant multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di])
	{
		assert forall k:: 0 <= k < di ==> d[k] in b[0..bi];
		
		b[bi] := c[ci];
		assert forall k:: 0 <= k < di ==> d[k] in b[0..bi];
		L(b[..], bi, c[..], ci);
		//==>

		assert forall k:: 0 <= k < ci+1 ==> c[k] in b[0..bi+1];
		assert forall k:: 0 <= k < di ==> d[k] in b[0..bi+1];

		ci := ci+1;

		assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi+1];
		assert forall k:: 0 <= k < di ==> d[k] in b[0..bi+1];

		bi := bi+1;

		assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi];
		assert forall k:: 0 <= k < di ==> d[k] in b[0..bi];
	}

	while(di < d.Length)
		invariant 0 <= bi <= b.Length && 0 <= ci <= c.Length && 0 <= di <= d.Length
		invariant bi == ci+di
		invariant SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
		invariant SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
		invariant forall k:: 0 <= k < ci ==> c[k] in b[0..bi]
		invariant forall k:: 0 <= k < di ==> d[k] in b[0..bi]
		invariant forall ck:: 0 <= ck < ci ==> b[bi-1] >= c[ck]
		invariant bi >= di && bi >= ci
		invariant if di < d.Length then forall k:: 0 <= k < bi ==> b[k] <= d[di] else true
		invariant if ci < c.Length then forall k:: 0 <= k < bi ==> b[k] <= c[ci] else true
		invariant multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di])
	{
		
		assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi];
		
		b[bi] := d[di];
		assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi];
		L(b[..], bi, d[..], di);
		//==>
		assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi+1];
		assert forall k:: 0 <= k < di+1 ==> d[k] in b[0..bi+1];
		
		di := di+1;

		assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi+1];
		assert forall k:: 0 <= k < di ==> d[k] in b[0..bi+1];

		bi := bi+1;

		assert forall k:: 0 <= k < ci ==> c[k] in b[0..bi];
		assert forall k:: 0 <= k < di ==> d[k] in b[0..bi];
	}

	assert multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di]);

	L3(b[..], bi, c[..], ci, d[..], di);
	assert Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..]);
}


lemma L(b:seq<int>, bi:nat, s:seq<int>, si:nat)
	requires 0 <= bi < |b| && 0 <= si < |s|
	requires forall k:: 0 <= k < si ==> s[k] in b[0..bi]
	requires b[bi] == s[si]
	ensures forall k:: 0 <= k < si+1 ==> s[k] in b[0..bi+1]
{}

lemma L3(b:seq<int>, bi:nat, s1:seq<int>, s1i:nat, s2:seq<int>, s2i:nat)
	requires 0 <= bi == |b| && 0 <= s1i == |s1| && 0 <= s2i == |s2|
	requires multiset(b[..bi]) == multiset(s1[..s1i]) + multiset(s2[..s2i])
	ensures multiset(b) == multiset(s1)+multiset(s2)
{
	assert multiset(b[..bi]) == multiset(s1[..s1i]) + multiset(s2[..s2i]);
	assert 0 <= bi == |b| && 0 <= s1i == |s1| && 0 <= s2i == |s2|;
	//==>
	assert multiset(b[..|b|]) == multiset(s1[..|s1|]) + multiset(s2[..|s2|]);
	mulset2(b, b[..|b|]);
	mulset2(s1, s1[..|s1|]);
	mulset2(s2, s2[..|s2|]);
	//==>
	assert multiset(b) == multiset(s1)+multiset(s2);
}

lemma mulset2(a: seq<int>, b: seq<int>)
	requires a == b
	ensures multiset(a) == multiset(b)
{}

lemma mulset(a: array<int>)
	ensures forall i:: 0 <= i < a.Length ==> multiset(a[..]) == multiset(a[0..i]) + multiset(a[i..a.Length])
{
	assert forall i:: 0 <= i < a.Length ==> a[..] == a[0..i] + a[i..a.Length];
	//==>
	assert forall i:: 0 <= i < a.Length ==> multiset(a[..]) == multiset(a[0..i]) + multiset(a[i..a.Length]);
}
/*
lemma L2(b:seq<int>, bi:nat, s1:seq<int>, s1i:nat, s2:seq<int>, s2i:nat)
	requires 0 <= bi < |b| && 0 <= s1i < |s1| && 0 <= s2i < |s2|
	requires multiset(b[..bi]) == multiset(s1[..s1i]) + multiset(s2[..s2i])
	requires b[bi] == s2[s2i]
	//requires |b[..bi]| == |s1[..s1i]| + |s2[..s2i]|
	ensures multiset(b[..bi+1]) == multiset(s1[..s1i]) + multiset(s2[..s2i+1])
{
	assert multiset(b[..bi]) == multiset(s1[..s1i]) + multiset(s2[..s2i]);
	assert b[bi] == s2[s2i];

	assert multiset(b[..bi+1]) == multiset(s1[..s1i]) + multiset(s2[..s2i+1]);
}
*/
method Main() {
	var a := new int[3];
	a[0], a[1], a[2] := 4, 8, 6;
	var q0 := a[..];
	assert q0 == [4,8,6];
	a := MergeSort(a);
	assert a.Length == |q0| && multiset(a[..]) == multiset(q0);
	print "the sorted version of [4, 8, 6] is ";
	print a[..];
	assert Sorted(a);
	assert a[..] == [4,6,8];
}
