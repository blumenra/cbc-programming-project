datatype Tree = Empty | Node(int,Tree,Tree)

method Main() {
	var tree := BuildBST([2,7,3,8,4,-2,9,0]);
	PrintTreeNumbersInorder(tree);
}

method PrintTreeNumbersInorder(t: Tree)
{
	match t {
		case Empty =>
		case Node(n, l, r) =>
			PrintTreeNumbersInorder(l);
			print n;
			print "\n";
			PrintTreeNumbersInorder(r);
	}
}

function NumbersInTree(t: Tree): set<int>
{
	NumbersInSequence(Inorder(t))
}

function NumbersInSequence(q: seq<int>): set<int>
{
	set x | x in q
}

predicate BST(t: Tree)
{
	Ascending(Inorder(t))
}

function Inorder(t: Tree): seq<int>
{
	match t {
		case Empty => []
		case Node(n',nt1,nt2) => Inorder(nt1)+[n']+Inorder(nt2)
	}
}

predicate Ascending(q: seq<int>)
{
	forall i,j :: 0 <= i < j < |q| ==> q[i] < q[j]
}

predicate NoDuplicates(q: seq<int>) { forall i,j :: 0 <= i < j < |q| ==> q[i] != q[j] }

method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
	
	
	var i:nat := 0;
	
	t := Empty;
	
	while(i < |q|)
	invariant 0 <= i <= |q|
	invariant BST(t)
	invariant NumbersInTree(t) == NumbersInSequence(q[0..i])
	{
		t := InsertBST(t, q[i]);
		i := i+1;
	}
}

method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
{
	match t0 {
		case Empty => t := Node(x, Empty, Empty);
		case Node(n',nt1,nt2) => 
			if(x < n')
			{
				LemmaBinarySearchSubtree(n',nt1,nt2);
				var tLeft := InsertBST(nt1, x);
				t := Node(n', tLeft, nt2);
				L_BST(n', nt1, nt2);
				/*
				assert BST(t0);
				assert greaterThanTree(nt1, n');
				//==>
				assert greaterThanTree(tLeft, n');
				assert smallerThanTree(nt2, n');
				*/
				//L(n', tLeft, nt2);
				L_greater(nt1, n', x, tLeft);

				assert BST(t);
			}
			else
			{
				
				LemmaBinarySearchSubtree(n',nt1,nt2);
				var tRight:Tree := InsertBST(nt2, x);
				t := Node(n', nt1, tRight);
				L_BST(n', nt1, nt2);
				
				/*
				assert BST(t0);
				assert greaterThanTree(nt1, n');
				
				assert smallerThanTree(nt2, n');
				assert n' < x;
				assert NumbersInTree(tRight) == NumbersInTree(nt2)+{x};
				//==>
				assert greaterThanTree(nt1, n');
				*/
				//assert smallerThanTree(tRight, n');
				
				L_smaller(nt2, n', x, tRight);

				assert NumbersInTree(t) == NumbersInTree(t0)+{x};

				assert BST(t);
				
			}
	}
}
/*
predicate tree_NoDuplicates(t:Tree)
{
	NoDuplicates(Inorder(t))
}
*/
lemma L3(t1:Tree, t2:Tree, x:int)
	requires NumbersInTree(t1) == NumbersInTree(t2)+{x}
	ensures forall i:: 0 <= i < |Inorder(t1)| ==> Inorder(t1)[i] in Inorder(t2) || Inorder(t1)[i] == x
	ensures forall i:: 0 <= i < |Inorder(t2)| ==> Inorder(t2)[i] in Inorder(t1)
{
	var q1 := Inorder(t1);
	var q2 := Inorder(t2);

	assert NumbersInTree(t1) == NumbersInTree(t2)+{x};
	//==>
	assert NumbersInSequence(q1) == NumbersInTree(t2)+{x};
	//==>
	assert forall i:: 0 <= i < |q1| ==> q1[i] in NumbersInTree(t1);
	assert forall i:: 0 <= i < |q2| ==> q2[i] in NumbersInTree(t1);
	//==>
	assert forall i:: 0 <= i < |q2| ==> q2[i] in q1;
	assert forall i:: 0 <= i < |q1| ==> q1[i] in q2 || q1[i] == x;
}


lemma L_smaller(nt2:Tree, n':int, x:int, tRight:Tree)
	requires smallerThanTree(nt2, n')
	requires n' < x
	requires NumbersInTree(tRight) == NumbersInTree(nt2)+{x}
	ensures smallerThanTree(tRight, n')

{
	
	L3(tRight, nt2, x);
	//==>
	assert forall i:: 0 <= i < |Inorder(tRight)| ==> n' < Inorder(tRight)[i];
	//==>
	assert smallerThanTree(tRight, n');
}

lemma L_greater(nt1:Tree, n':int, x:int, tLeft:Tree)
	requires greaterThanTree(nt1, n')
	requires x < n'
	requires NumbersInTree(tLeft) == NumbersInTree(nt1)+{x}
	ensures greaterThanTree(tLeft, n')
{
	L3(tLeft, nt1, x);
	//==>
	assert forall i:: 0 <= i < |Inorder(tLeft)| ==> Inorder(tLeft)[i] < n';
	//==>
	assert greaterThanTree(tLeft, n');
}
/*
lemma L_Ascending(q:seq<int>, x:int)
	requires Ascending(q+[x])
	ensures forall i:: 0 <= i < |q| ==> q[i] < x
*/

lemma L_BST(n: int, left: Tree, right: Tree)
	requires BST(Node(n, left, right))
	ensures greaterThanTree(left, n)
	ensures smallerThanTree(right, n)
{
	assert Ascending(Inorder(Node(n, left, right)));
	var qleft, qright := Inorder(left), Inorder(right);
	var q1 := qleft+[n]+qright;
	var q2 := qleft+[n];
	var q3 := [n]+qright;
	LemmaAscendingSubsequence(q1, q2, 0);
	LemmaAscendingSubsequence(q1, q3, |q2|-1);
	assert q2[|q2|-1] == n;

	//==>

	assert greaterThanTree(left, n);
	assert smallerThanTree(right, n);
}

predicate smallerThanTree(t:Tree, x:int)
{
	forall i:: 0 <= i < |Inorder(t)| ==> x < Inorder(t)[i]
}

predicate greaterThanTree(t:Tree, x:int)
{
	forall i:: 0 <= i < |Inorder(t)| ==> x > Inorder(t)[i]
}

lemma L(n: int, left: Tree, right: Tree)
	requires BST(left) && BST(right)
	requires forall i:: 0 <= i < |Inorder(left)| ==> n > Inorder(left)[i]
	requires forall i:: 0 <= i < |Inorder(right)| ==> n < Inorder(right)[i]
	ensures BST(Node(n, left, right))
{}

lemma	LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
	requires BST(Node(n, left, right))
	ensures BST(left) && BST(right)
{
	assert Ascending(Inorder(Node(n, left, right)));
	var qleft, qright := Inorder(left), Inorder(right);
	var q := qleft+[n]+qright;
	assert q == Inorder(Node(n, left, right));
	assert Ascending(qleft+[n]+qright);
	assert Ascending(qleft) by { LemmaAscendingSubsequence(q, qleft, 0); }
	assert Ascending(qright) by { LemmaAscendingSubsequence(q, qright, |qleft|+1); }
}

lemma LemmaAscendingSubsequence(q1: seq<int>, q2: seq<int>, i: nat)
	requires i <= |q1|-|q2| && q2 == q1[i..i+|q2|]
	requires Ascending(q1)
	ensures Ascending(q2)
{}
