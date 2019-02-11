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

		assert a[..] == leftSeq + rightSeq;

		copySeqToArray(leftSeq, leftArr);
		copySeqToArray(rightSeq, rightArr);
		//==>
		assert leftSeq == leftArr[..] && rightSeq == rightArr[..];
		//==>
		assert a[..] == leftArr[..] + rightArr[..];
		//==>
		assert multiset(a[..]) == multiset(leftArr[..])+multiset(rightArr[..]);

		var leftSortedArr := MergeSort(leftArr);

		assert multiset(a[..]) == multiset(leftArr[..])+multiset(rightArr[..]); // Still true after the assignment because MergeSort does not modify the given array
		
		var rightSortedArr := MergeSort(rightArr);

		assert multiset(a[..]) == multiset(leftArr[..])+multiset(rightArr[..]); // Still true after the assignment because MergeSort does not modify the given array

		Merge(b, leftSortedArr, rightSortedArr);
		//==>
		assert Sorted(b) && multiset(b[..]) == multiset(leftSortedArr[..])+multiset(rightSortedArr[..]);
		//==>
		assert multiset(a[..]) == multiset(leftSortedArr[..])+multiset(rightSortedArr[..]);
		//==>
		assert multiset(a[..]) == multiset(b[..]);
	}


	assert b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..]);
}

method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
{
	var bi, ci, di := Loop1(b, c, d);
	//==> 
	assert ci == c.Length || di == d.Length;

	if(ci == c.Length)
	{
		Loop2(b, d, c, bi, di, ci);
	}
	else
	{
		assert di == d.Length;
		Loop2(b, c, d, bi, ci, di);
	}

	assert Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..]);
}

method copySeqToArray(q:seq<int>, a:array<int>)
	requires |q| == a.Length
	ensures q == a[..]
	modifies a
{
	var i:nat := 0;

	while(i < a.Length)
	invariant 0 <= i <= a.Length
	invariant a[..i] == q[..i]
	{

		a[i] := q[i];
		i := i+1;
	}
}

method Loop1(b: array<int>, c: array<int>, d: array<int>) returns (bi:nat, ci:nat, di:nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	
	ensures  0 <= bi <= b.Length && 0 <= ci <= c.Length && 0 <= di <= d.Length
	ensures bi == ci+di
	ensures SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
	ensures multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di])
	ensures ci == c.Length || di == d.Length
	ensures preffixASmallerThanSuffixB(b, c, bi, ci) && preffixASmallerThanSuffixB(b, d, bi, di)

	modifies b
{
	bi, ci, di := 0, 0, 0;

	while(ci < c.Length && di < d.Length)
		invariant LoopsInv(b, c, d, bi, ci, di)

		decreases c.Length-ci
		decreases d.Length-di
	{
		
		if(c[ci] <= d[di]){
			
			b[bi] := c[ci];
			
			ci := ci+1;
		}
		else{
			
			b[bi] := d[di];
			
			di := di+1;
		}

		bi := bi+1;
	}
}

method Loop2(b: array<int>, arr1: array<int>, arr2: array<int>, bi0:nat, arr1i0:nat, arr2i0:nat) 
	requires b.Length == arr1.Length + arr2.Length
	requires 0 <= bi0 <= b.Length && 0 <= arr1i0 <= arr1.Length && 0 <= arr2i0 <= arr2.Length
	requires bi0 == arr1i0 + arr2i0
	requires SortedSequence(b[0..bi0]) && SortedSequence(arr1[..]) && SortedSequence(arr2[..])
	requires multiset(b[..bi0]) == multiset(arr1[..arr1i0]) + multiset(arr2[..arr2i0])
	requires arr2i0 == arr2.Length
	requires preffixASmallerThanSuffixB(b, arr1, bi0, arr1i0) && preffixASmallerThanSuffixB(b, arr2, bi0, arr2i0)

	ensures Sorted(b)
	ensures multiset(b[..]) == multiset(arr1[..])+multiset(arr2[..])

	modifies b
{
	var bi, arr1i, arr2i := bi0, arr1i0, arr2i0;

	while(arr1i < arr1.Length)
		invariant LoopsInv(b, arr1, arr2, bi, arr1i, arr2i)
	{		
		b[bi] := arr1[arr1i];

		arr1i:= arr1i+1;

		bi := bi+1;
	}

	assert arr2i == arr2.Length; // From pre-condition and the fact that the while loop didn't updated di
	assert arr1i == arr1.Length; // From while inv "0 <= ci <= c.Length" + NOT(guard) "ci >= c.Length"
	assert bi == b.Length; // From while inv "bi == ci+di" + above 2 assertions
	assert multiset(b[..bi]) == multiset(arr1[..arr1i]) + multiset(arr2[..arr2i]); // From while inv
	multiset_L(b, arr1, arr2, bi, arr1i, arr2i);
	// ==>
	assert multiset(b[..]) == multiset(arr1[..])+multiset(arr2[..]);
	
	
	assert bi == b.Length;
	assert SortedSequence(b[0..bi]); // From while inv
	L1(b, bi);
	// ==>
	assert Sorted(b);
}

predicate LoopsInv(b: array<int>, arr1: array<int>, arr2: array<int>, bi:nat, arr1i:nat, arr2i:nat)
	reads b, arr1, arr2
{
	0 <= bi <= b.Length && 0 <= arr1i <= arr1.Length && 0 <= arr2i <= arr2.Length &&
	bi == arr1i + arr2i &&
	multiset(b[..bi]) == multiset(arr1[..arr1i]) + multiset(arr2[..arr2i]) &&
	preffixASmallerThanSuffixB(b, arr1, bi, arr1i) &&
	preffixASmallerThanSuffixB(b, arr2, bi, arr2i) &&
	SortedSequence(b[0..bi]) && SortedSequence(arr1[..]) && SortedSequence(arr2[..])
}


/*
All the numbers in @a until index @ai are smaller than each number in @b from index @bi to the end
*/
predicate preffixASmallerThanSuffixB(a: array<int>, b: array<int>, ai:nat, bi:nat)
	requires ai <= a.Length
	reads a,b
{
	forall i,j:: 0 <= i < ai && bi <= j < b.Length ==> a[i] <= b[j]
}

lemma L1(b:array<int>, bi:nat)
	requires bi == b.Length
	requires SortedSequence(b[0..bi])
	ensures Sorted(b)
{}

lemma multiset_L(b: array<int>, c: array<int>, d: array<int>, bi:nat, ci:nat, di:nat)
	requires bi == b.Length
	requires ci == c.Length
	requires di == d.Length
	requires multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di])
	ensures  multiset(b[..]) == multiset(c[..])+multiset(d[..])
{
	seq_L(b[..]);
	seq_L(c[..]);
	seq_L(d[..]);
}

lemma seq_L(q:seq<int>)
	ensures q[..] == q[0..|q|]
{}


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
