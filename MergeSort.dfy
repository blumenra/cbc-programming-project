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
	
	if(ci == c.Length)
	{
		Loop2(b, d, c, bi, di, ci);
	}
	else
	{
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
	ensures  SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
	ensures  multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di])
	ensures ci == c.Length || di == d.Length
	ensures subarraySetByIndex(c, ci, b, bi)
	ensures subarraySetByIndex(d, di, b, bi)
	ensures pred(b, c, bi, ci)
	ensures pred(b, d, bi, di)

	modifies b
{
	bi := 0;
	ci := 0;
	di := 0;

	while(ci < c.Length && di < d.Length)
		invariant 0 <= bi <= b.Length && 0 <= ci <= c.Length && 0 <= di <= d.Length
		invariant bi == ci+di
		invariant SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
		invariant multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di])
		invariant subarraySetByIndex(c, ci, b, bi)
		invariant subarraySetByIndex(d, di, b, bi)
		invariant pred(b, c, bi, ci)
		invariant pred(b, d, bi, di)

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

method Loop2(b: array<int>, c: array<int>, d: array<int>, bi0:nat, ci0:nat, di0:nat) 
	requires b.Length == c.Length + d.Length
	requires 0 <= bi0 <= b.Length && 0 <= ci0 <= c.Length && 0 <= di0 <= d.Length
	requires bi0 == ci0+di0
	requires SortedSequence(b[0..bi0]) && SortedSequence(c[..]) && SortedSequence(d[..])
	requires multiset(b[..bi0]) == multiset(c[..ci0]) + multiset(d[..di0])
	requires di0 == d.Length
	requires subarraySetByIndex(d, di0, b, bi0)
	requires pred(b, c, bi0, ci0) && pred(b, d, bi0, di0)

	ensures Sorted(b)
	ensures multiset(b[..]) == multiset(c[..])+multiset(d[..])

	modifies b
{
	var bi, ci, di := bi0, ci0, di0;

	while(ci < c.Length)
		invariant 0 <= bi <= b.Length && 0 <= ci <= c.Length && 0 <= di <= d.Length
		invariant bi == ci+di
		invariant SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
		invariant multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di])
		invariant di == d.Length
		invariant forall i,j:: ci <= i < c.Length && 0 <= j < bi ==> b[j] <= c[i]
	{		
		b[bi] := c[ci];

		ci := ci+1;

		bi := bi+1;
	}

	assert bi == b.Length;
	assert SortedSequence(b[0..bi]); // while inv
	L1(b, bi);
	// ==>
	assert Sorted(b);


	assert bi == b.Length;
	assert ci == c.Length;
	assert di == d.Length;
	multiset_L(b, c, d, bi, ci, di);
	// ==>
	assert multiset(b[..]) == multiset(c[..])+multiset(d[..]);
}

predicate pred(a: array<int>, b: array<int>, ai:nat, bi:nat)
	requires ai <= a.Length
	reads a,b
{
	forall i,j:: 0 <= i < ai && bi <= j < b.Length ==> a[i] <= b[j]
}

predicate subarraySetByIndex(a:array<int>, ai:nat, b:array<int>, bi:nat)
	requires 0 <= ai <= a.Length
	requires 0 <= bi <= b.Length
	reads a, b
{
	multiset(a[..ai]) <= multiset(b[..bi])
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
