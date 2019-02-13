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
	//alternation
	if(Guard1(a)){
		b:=MS1(a,b);
		
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
		//==>
		assert leftSortedArr.Length == leftArr.Length && Sorted(leftSortedArr) && multiset(leftArr[..]) == multiset(leftSortedArr[..]);//post condition of recursive call
		//==>
		assert multiset(leftSortedArr[..]) == multiset(leftArr[..]);
		//==>
		assert multiset(a[..]) == multiset(leftSortedArr[..]) + multiset(rightArr[..]);
		

		var rightSortedArr := MergeSort(rightArr);
		//==>
		assert rightSortedArr.Length == rightArr.Length && Sorted(rightSortedArr) && multiset(rightArr[..]) == multiset(rightSortedArr[..]);//post condition of recursive call
		//==>
		assert multiset(rightSortedArr[..]) == multiset(rightArr[..]);
		//==>
		assert multiset(a[..]) == multiset(leftSortedArr[..]) + multiset(rightSortedArr[..]);


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

predicate method Guard1(a: array<int>)
	requires 0<=a.Length
{
	a.Length <= 1
}

method MS1(a: array<int>,b0: array<int>) returns (b: array<int>)
	 requires Guard1(a)
	 ensures b.Length == a.Length && Sorted(b) && multiset(a[..]) == multiset(b[..])
{	

	b:=b0;
	// assignment
	LemmaUpdateb(a,b);
	b := a;

}

lemma LemmaUpdateb(a: array<int>,b: array<int>)
	requires Guard1(a)
	ensures a.Length == a.Length && Sorted(a) && multiset(a[..]) == multiset(a[..])
{}

method Merge(b: array<int>, c: array<int>, d: array<int>)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)

	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b
{



	var bi, ci, di := Loop1(b, c, d); // introduce local variable + strengthen postcondition
	//==> 
	assert ci == c.Length || di == d.Length;
	Merga_alt(b, d, c, bi, di, ci);

	
}



predicate method Guard2(ci:nat,c:array<int>)
{
	ci == c.Length
} 

method Merga_alt(b: array<int>, d: array<int>, c: array<int>, bi:nat, di:nat, ci:nat)
	
	requires  0 <= bi <= b.Length && 0 <= ci <= c.Length && 0 <= di <= d.Length
	requires bi == ci+di
	requires SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
	requires multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di])
	requires ci == c.Length || di == d.Length
	requires preffixASmallerThanSuffixB(b, c, bi, ci) && preffixASmallerThanSuffixB(b, d, bi, di)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)

	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b;

	{

	//alternation
	if(Guard2(ci,c))
	{
		Merga_alt_alt1(b, d, c, bi, di, ci);	
			
	}
	else
	{
		assert di == d.Length;
		Merga_alt_alt2(b, d, c, bi, di, ci);

	}


	}

method Merga_alt_alt1(b: array<int>, d: array<int>, c: array<int>, bi:nat, di:nat, ci:nat) 

	requires  0 <= bi <= b.Length && 0 <= ci <= c.Length && 0 <= di <= d.Length
	requires bi == ci+di
	requires SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
	requires multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di])
	requires ci == c.Length || di == d.Length
	requires preffixASmallerThanSuffixB(b, c, bi, ci) && preffixASmallerThanSuffixB(b, d, bi, di)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	requires Guard2(ci,c)

	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b;
	{
	

	Loop2(b, d, c, bi, di, ci);

	}

method Merga_alt_alt2(b: array<int>, d: array<int>, c: array<int>, bi:nat, di:nat, ci:nat) 

	requires  0 <= bi <= b.Length && 0 <= ci <= c.Length && 0 <= di <= d.Length
	requires bi == ci+di
	requires SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
	requires multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di])
	requires ci == c.Length || di == d.Length
	requires preffixASmallerThanSuffixB(b, c, bi, ci) && preffixASmallerThanSuffixB(b, d, bi, di)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	requires !Guard2(ci,c)

	ensures Sorted(b) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
	modifies b;
	{
	

	Loop2(b, c, d, bi, ci, di);

	}

	




method copySeqToArray(q:seq<int>, a:array<int>)
	requires |q| == a.Length
	ensures q == a[..]
	modifies a
{

	var i:nat; // introduce local variable + strengthen postcondition
	i:=copySeqToArray_Help(q,a);
	Lemma1(q,a,i);

	
}

lemma Lemma1(q:seq<int>, a:array<int>,i:nat)
	requires Inv_copySeqToArray(q,a,i) && !Guard_Loop_copySeqToArray_Help(a,i)
	ensures q == a[..]
{}


method copySeqToArray_Help(q:seq<int>, a:array<int>) returns (i:nat)
	requires |q| == a.Length

	ensures Inv_copySeqToArray(q,a,i) && !Guard_Loop_copySeqToArray_Help(a,i)
	modifies a
{


	// sequential composition
	i:=Init_copySeqToArray_Help(q,a);
	i:=Loop_copySeqToArray_Help(q,a,i);


}

method Loop_copySeqToArray_Help(q:seq<int>, a:array<int>,i0:nat) returns (i:nat)
	requires |q| == a.Length
	requires Inv_copySeqToArray(q,a,i0)

	ensures Inv_copySeqToArray(q,a,i) &&  !Guard_Loop_copySeqToArray_Help(a,i)
	modifies a
{


	i:=i0;
	// iteration
	while(Guard_Loop_copySeqToArray_Help(a,i))
	invariant Inv_copySeqToArray(q,a,i)
	decreases a.Length-i
	{
		i:=Loop_body_copySeqToArray_Help(q,a,i);
		
	}


}

predicate method Guard_Loop_copySeqToArray_Help(a:array<int>,i:nat)
{
	i < a.Length
}


method Loop_body_copySeqToArray_Help(q:seq<int>, a:array<int>,i0:nat) returns (i:nat)
	requires |q| == a.Length 
	requires Inv_copySeqToArray(q,a,i0) && Guard_Loop_copySeqToArray_Help(a,i0)

	ensures Inv_copySeqToArray(q,a,i) && 0<=a.Length-i<a.Length-i0
	ensures i0<i
	modifies a
{
	

	i:=i0;
	a[i] := q[i];
	L_update(q,a,i);
	i := i+1;//assignemnt

	
	

}

lemma L_update(q:seq<int>, a:array<int>,i:nat)
	requires |q| == a.Length 
	requires Inv_copySeqToArray(q,a,i) && Guard_Loop_copySeqToArray_Help(a,i)
	requires a[i] ==q[i]

	ensures Inv_copySeqToArray(q,a,i+1) && 0<=a.Length-(i+1)< a.Length-i
	ensures i<i+1
{}



method Init_copySeqToArray_Help(q:seq<int>, a:array<int>) returns (i:nat)
	requires |q| == a.Length
	ensures Inv_copySeqToArray(q,a,i)
{

// assignment
	LemmaInit_copySeqToArray_Help(q,a);
	i:=0;


}

lemma LemmaInit_copySeqToArray_Help(q: seq<int>,  a:array<int>)
	requires |q| == a.Length
	ensures Inv_copySeqToArray(q,a,0)
{}

predicate  Inv_copySeqToArray(q:seq<int>, a:array<int>,i:nat)
reads a;
{
	0 <= i <= a.Length==|q| && a[..i] == q[..i]
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
	

	bi, ci, di := Init_Loop1(b,c,d);
	bi,ci,di:=Loop_Loop1(b,c,d,bi,ci,di);
	lemama_end_loop1(b,c,d,bi,ci,di);


	
}

lemma lemama_end_loop1(b: array<int>, c: array<int>, d: array<int>,bi:nat, ci:nat, di:nat)
	requires !Guard_Loop1(c,d,ci,di) && LoopsInv(b, c, d, bi, ci, di)

	ensures  0 <= bi <= b.Length && 0 <= ci <= c.Length && 0 <= di <= d.Length
	ensures bi == ci+di
	ensures SortedSequence(b[0..bi]) && SortedSequence(c[..]) && SortedSequence(d[..])
	ensures multiset(b[..bi]) == multiset(c[..ci]) + multiset(d[..di])
	ensures ci == c.Length || di == d.Length
	ensures preffixASmallerThanSuffixB(b, c, bi, ci) && preffixASmallerThanSuffixB(b, d, bi, di)
{}





method Loop_Loop1(b: array<int>, c: array<int>, d: array<int>,bi0:nat, ci0:nat, di0:nat) returns(bi:nat, ci:nat, di:nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	requires LoopsInv(b, c, d, bi0, ci0, di0)

	ensures  !Guard_Loop1(c,d,ci,di) && LoopsInv(b, c, d, bi, ci, di)
	modifies b
	{


	bi, ci, di:=bi0,ci0,di0;
	//iterartion
	while(Guard_Loop1(c,d,ci,di))
	invariant LoopsInv(b, c, d, bi, ci, di)
	decreases c.Length-ci 
	decreases d.Length-di
	{
		// following assignment + contract frame
		ci,di:=Loop_body_Loop1(b,c,d,bi,ci,di);
		bi := bi+1;
	}


	}


method Init_Loop1(b: array<int>, c: array<int>, d: array<int>) returns (bi:nat, ci:nat, di:nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)

	ensures LoopsInv(b, c, d, bi, ci, di)
	{



	// assignment
	Lemma_Init_Loop1(b,c,d);
	bi, ci, di:=0,0,0;


	}

lemma Lemma_Init_Loop1(b: array<int>, c: array<int>, d: array<int>) 
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)

	ensures LoopsInv(b, c, d, 0,0,0)
	{}



predicate method Guard_Loop1(c: array<int>, d: array<int>,ci:nat, di:nat)
	
{
	ci < c.Length && di < d.Length
}

method Loop_body_Loop1 (b: array<int>, c: array<int>, d: array<int>,bi:nat, ci0:nat, di0:nat) returns ( ci:nat, di:nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	requires LoopsInv(b, c, d, bi, ci0, di0 ) && Guard_Loop1(c,d,ci0,di0)

	ensures LoopsInv(b, c, d, bi+1, ci, di) && (0<=c.Length - ci <= c.Length-ci0 && 0<=d.Length-di <= d.Length-di0)
	modifies b;
{

	

	ci:=ci0;
	di:=di0;
	// alternation + contract frame (*2)
	if(Guard_Loop_body_Loop1(c,d,ci,di)){
		
		ci:=Loop_body_Loop1_update_ci(b,c,d,bi,ci,di);
			
	}
	else{
		
		di:=Loop_body_Loop1_update_di(b,c,d,bi,ci,di);
	}

}

predicate method Guard_Loop_body_Loop1(c: array<int>, d: array<int>,ci:nat, di:nat)
	requires ci< c.Length
	requires di< d.Length
	reads c ,d 
{
	c[ci] <= d[di]
}


method Loop_body_Loop1_update_ci (b: array<int>, c: array<int>, d: array<int>,bi:nat, ci0:nat, di:nat) returns ( ci:nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	requires LoopsInv(b, c, d, bi, ci0, di) && Guard_Loop1(c,d,ci0,di) && Guard_Loop_body_Loop1(c,d,ci0,di)

	ensures LoopsInv(b, c, d, bi+1, ci, di) && (0<=c.Length - ci < c.Length-ci0 && 0<=d.Length-di == d.Length-di)
	ensures ci0<ci
	modifies b
{

	
	
	ci:=ci0;
	//assignemnt
	b[bi] := c[ci];
	LemmaUpdateci(b,c,d,bi,ci,di);
	ci := ci+1;

	

}

method Loop_body_Loop1_update_di (b: array<int>, c: array<int>, d: array<int>,bi:nat, ci:nat, di0:nat) returns ( di:nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	requires LoopsInv(b, c, d, bi, ci, di0) && Guard_Loop1(c,d,ci,di0) && !(Guard_Loop_body_Loop1(c,d,ci,di0))

	ensures LoopsInv(b, c, d, bi+1, ci, di) && (0<=c.Length - ci == c.Length-ci && 0<=d.Length-di < d.Length-di0)
	ensures di0<di
	modifies b
{
	

	di:=di0;
	b[bi] := d[di];
	LemmaUpdatedi(b,c,d,bi,ci,di);//assignemnt
	di := di+1;



}

lemma LemmaUpdateci(b: array<int>, c: array<int>, d: array<int>,bi:nat, ci:nat, di:nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	requires LoopsInv(b, c, d, bi, ci, di) && Guard_Loop1(c,d,ci,di) && Guard_Loop_body_Loop1(c,d,ci,di)
	requires b[bi] == c[ci];

	ensures LoopsInv(b, c, d, bi+1, ci+1, di) && (0<=c.Length - (ci+1) < c.Length-ci) && (0<=d.Length-di == d.Length-di)
	ensures ci<ci+1
{}

lemma LemmaUpdatedi(b: array<int>, c: array<int>, d: array<int>,bi:nat, ci:nat, di:nat)
	requires b != c && b != d && b.Length == c.Length + d.Length
	requires Sorted(c) && Sorted(d)
	requires LoopsInv(b, c, d, bi, ci, di) && Guard_Loop1(c,d,ci,di) && !(Guard_Loop_body_Loop1(c,d,ci,di))
	requires b[bi] == d[di]

	ensures LoopsInv(b, c, d, bi+1, ci, di+1) &&  (0<=c.Length - ci == c.Length-ci && d.Length-di > d.Length-(di+1)>=0)
	ensures di<di+1
{}


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


// introduce local variable + strengthen postcondition
	var bi, arr1i, arr2i;
	bi, arr1i, arr2i:=Loop2_help(b,arr1,arr2,bi0,arr1i0,arr2i0);
	lemma_end_loop(b,arr1,arr2,bi,arr1i,arr2i);



}

lemma lemma_end_loop(b: array<int>, arr1: array<int>, arr2: array<int>, bi:nat, arr1i:nat, arr2i:nat)
	requires bi == b.Length;
	requires  arr2i == arr2.Length
	requires LoopsInv(b, arr1, arr2, bi, arr1i, arr2i) && !Guard_Loop2(arr1i,arr1) 

	ensures  Sorted(b)
	ensures multiset(b[..]) == multiset(arr1[..])+multiset(arr2[..])
{
	
	assert  LoopsInv(b, arr1, arr2, bi, arr1i, arr2i) && !Guard_Loop2(arr1i,arr1) ;

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



method Loop2_help(b: array<int>, arr1: array<int>, arr2: array<int>, bi0:nat, arr1i0:nat, arr2i0:nat) returns (bi:nat, arr1i:nat, arr2i:nat) 
	requires b.Length == arr1.Length + arr2.Length
	requires 0 <= bi0 <= b.Length && 0 <= arr1i0 <= arr1.Length && 0 <= arr2i0 <= arr2.Length
	requires bi0 == arr1i0 + arr2i0
	requires SortedSequence(b[0..bi0]) && SortedSequence(arr1[..]) && SortedSequence(arr2[..])
	requires multiset(b[..bi0]) == multiset(arr1[..arr1i0]) + multiset(arr2[..arr2i0])
	requires arr2i0 == arr2.Length
	requires preffixASmallerThanSuffixB(b, arr1, bi0, arr1i0) && preffixASmallerThanSuffixB(b, arr2, bi0, arr2i0)


	ensures LoopsInv(b, arr1, arr2, bi, arr1i, arr2i) && !Guard_Loop2(arr1i,arr1)
	ensures  arr2i == arr2.Length

	modifies b
{
	
	
	// sequential composition
	bi, arr1i, arr2i:=Init_Loop2(b,arr1,arr2,bi0,arr1i0,arr2i0);
	bi, arr1i, arr2i:=Loop_Loop2(b,arr1,arr2,bi,arr1i, arr2i);




}


method Loop_Loop2(b: array<int>, arr1: array<int>, arr2: array<int>, bi0:nat, arr1i0:nat, arr2i0:nat)returns (bi:nat, arr1i:nat, arr2i:nat) 
	requires b.Length == arr1.Length + arr2.Length
	requires 0 <= bi0 <= b.Length && 0 <= arr1i0 <= arr1.Length && 0 <= arr2i0 <= arr2.Length
	requires bi0 == arr1i0 + arr2i0
	requires SortedSequence(b[0..bi0]) && SortedSequence(arr1[..]) && SortedSequence(arr2[..])
	requires multiset(b[..bi0]) == multiset(arr1[..arr1i0]) + multiset(arr2[..arr2i0])
	requires arr2i0 == arr2.Length
	requires preffixASmallerThanSuffixB(b, arr1, bi0, arr1i0) && preffixASmallerThanSuffixB(b, arr2, bi0, arr2i0)
	requires LoopsInv(b, arr1, arr2, bi0, arr1i0, arr2i0)

	ensures LoopsInv(b, arr1, arr2, bi, arr1i, arr2i) && !Guard_Loop2(arr1i,arr1)
	ensures  arr2i == arr2.Length

	modifies b;
{
	

		
	bi,arr1i,arr2i:=bi0,arr1i0,arr2i0;
	//iteration
	while(Guard_Loop2(arr1i,arr1))
	invariant LoopsInv(b, arr1, arr2, bi, arr1i, arr2i)
	decreases arr1.Length-arr1i
	{		
		
		bi,arr1i:=Loop_Loop2_Body(b, arr1, arr2, bi, arr1i, arr2i);
	}



}

predicate method Guard_Loop2(arr1i:nat,arr1: array<int>)
{
	arr1i < arr1.Length
}

method Loop_Loop2_Body(b: array<int>, arr1: array<int>, arr2: array<int>, bi0:nat, arr1i0:nat, arr2i0:nat)returns (bi:nat, arr1i:nat)
	requires b.Length == arr1.Length + arr2.Length
	requires 0 <= bi0 <= b.Length && 0 <= arr1i0 <= arr1.Length && 0 <= arr2i0 <= arr2.Length
	requires bi0 == arr1i0 + arr2i0
	requires SortedSequence(b[0..bi0]) && SortedSequence(arr1[..]) && SortedSequence(arr2[..])
	requires multiset(b[..bi0]) == multiset(arr1[..arr1i0]) + multiset(arr2[..arr2i0])
	requires arr2i0 == arr2.Length
	requires preffixASmallerThanSuffixB(b, arr1, bi0, arr1i0) && preffixASmallerThanSuffixB(b, arr2, bi0, arr2i0)
	requires LoopsInv(b, arr1, arr2, bi0, arr1i0, arr2i0) && Guard_Loop2(arr1i0,arr1)

	ensures LoopsInv(b, arr1, arr2, bi, arr1i, arr2i0) && 0<=arr1.Length-arr1i< arr1.Length-arr1i0 
	ensures arr1i0<arr1i
	ensures bi>bi0
	modifies b;
{
	
		
	bi,arr1i:=bi0,arr1i0;
	b[bi] := arr1[arr1i];
	Lemma_as_Loop_Loop2_Body(b,arr1,arr2,bi0,arr1i0,arr2i0);
	arr1i:= arr1i+1;
	bi := bi+1;

	

}

lemma Lemma_as_Loop_Loop2_Body(b: array<int>, arr1: array<int>, arr2: array<int>, bi0:nat, arr1i0:nat, arr2i0:nat)
	requires b.Length == arr1.Length + arr2.Length
	requires 0 <= bi0 <= b.Length && 0 <= arr1i0 <= arr1.Length && 0 <= arr2i0 <= arr2.Length
	requires bi0 == arr1i0 + arr2i0
	requires SortedSequence(b[0..bi0]) && SortedSequence(arr1[..]) && SortedSequence(arr2[..])
	requires multiset(b[..bi0]) == multiset(arr1[..arr1i0]) + multiset(arr2[..arr2i0])
	requires arr2i0 == arr2.Length
	requires preffixASmallerThanSuffixB(b, arr1, bi0, arr1i0) && preffixASmallerThanSuffixB(b, arr2, bi0, arr2i0)
	requires LoopsInv(b, arr1, arr2, bi0, arr1i0, arr2i0) && Guard_Loop2(arr1i0,arr1)
	requires b[bi0] == arr1[arr1i0];

	ensures LoopsInv(b, arr1, arr2, bi0+1, arr1i0+1, arr2i0) && 0<=arr1.Length-(arr1i0+1)< arr1.Length-arr1i0 
	ensures arr1i0<arr1i0+1
	ensures bi0+1>bi0
{}




method Init_Loop2(b: array<int>, arr1: array<int>, arr2: array<int>, bi0:nat, arr1i0:nat, arr2i0:nat)returns (bi:nat, arr1i:nat, arr2i:nat) 
	requires b.Length == arr1.Length + arr2.Length
	requires 0 <= bi0 <= b.Length && 0 <= arr1i0 <= arr1.Length && 0 <= arr2i0 <= arr2.Length
	requires bi0 == arr1i0 + arr2i0
	requires SortedSequence(b[0..bi0]) && SortedSequence(arr1[..]) && SortedSequence(arr2[..])
	requires multiset(b[..bi0]) == multiset(arr1[..arr1i0]) + multiset(arr2[..arr2i0])
	requires arr2i0 == arr2.Length
	requires preffixASmallerThanSuffixB(b, arr1, bi0, arr1i0) && preffixASmallerThanSuffixB(b, arr2, bi0, arr2i0)

	ensures bi==bi0 && arr1i==arr1i0 &&  arr2i==arr2i0 
	ensures arr2i == arr2.Length
	ensures LoopsInv(b, arr1, arr2, bi, arr1i, arr2i)
	 
	{

	
	LemmaInit_Loop2(b,arr1,arr2,bi0,arr1i0,arr2i0);
	bi, arr1i, arr2i := bi0, arr1i0, arr2i0;

	
	}


lemma LemmaInit_Loop2(b: array<int>, arr1: array<int>, arr2: array<int>, bi0:nat, arr1i0:nat, arr2i0:nat)
	requires b.Length == arr1.Length + arr2.Length
	requires 0 <= bi0 <= b.Length && 0 <= arr1i0 <= arr1.Length && 0 <= arr2i0 <= arr2.Length
	requires bi0 == arr1i0 + arr2i0
	requires SortedSequence(b[0..bi0]) && SortedSequence(arr1[..]) && SortedSequence(arr2[..])
	requires multiset(b[..bi0]) == multiset(arr1[..arr1i0]) + multiset(arr2[..arr2i0])
	requires arr2i0 == arr2.Length
	requires preffixASmallerThanSuffixB(b, arr1, bi0, arr1i0) && preffixASmallerThanSuffixB(b, arr2, bi0, arr2i0)

	ensures arr2i0 == arr2.Length
	ensures LoopsInv(b, arr1, arr2, bi0, arr1i0, arr2i0)
{}

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
