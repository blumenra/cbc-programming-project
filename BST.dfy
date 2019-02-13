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
	

	var i:nat;// introduce local variable + strengthen postcondition
	i,t:=BuildBST2(q);
	LemmaX(q,i,t);
	
}

method BuildBST2(q: seq<int>) returns  (i:nat ,t :Tree)
requires NoDuplicates(q)
ensures Inv(q,t,i) && !Guard1(q,i,t)
{
	

	// sequential composition
	i,t:=Init(q);
	i,t:=Loop(q,i,t);



}

method Loop(q: seq<int>,i0:nat,t0:Tree) returns  (i:nat ,t :Tree)
requires  Inv(q,t0,i0) && NoDuplicates(q)
ensures  Inv(q,t,i) && !Guard1(q,i,t)
{


	i:=i0;
	t:=t0;
	//iteration
	while(Guard1(q,i,t))
	invariant Inv(q,t,i)
	decreases V(q,i)
	{
		
		i,t:=LoopBody(q,i,t);

	}

	
}

method LoopBody(q: seq<int>,i0:nat,t0:Tree) returns  (i:nat ,t :Tree)
requires  Inv(q,t0,i0) && Guard1(q,i0,t0) && NoDuplicates(q)
ensures Inv(q,t,i) && 0 <= V(q,i) < V(q,i0)
{

		i:=i0;
		t:=t0;
		
		t := InsertBST(t, q[i]); 
		LemmaI(q,i,t,t0); //assignment
		i:=i+1; 
		LemmaWhile(q,i,t,i0,t0);

		

}
function V(q:seq<int>,i:nat): int
{
	|q|-i
}

predicate  Inv(q: seq<int> ,t: Tree,i:nat)
{
	 0 <= i <= |q| && 
	 BST(t) &&
	 NumbersInTree(t) == NumbersInSequence(q[0..i])
}




lemma LemmaI(q: seq<int>,i:nat,t:Tree,t0:Tree)
	requires Inv(q,t0,i);
	requires  0 <= i < |q|
	requires BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{q[i]}
	ensures Inv(q,t,i+1);
	ensures i < i+1
{}




lemma LemmaX(q: seq<int>,i:nat,t:Tree)
requires Inv(q,t,i)
requires !Guard1(q,i,t)
ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{}


lemma LemmaWhile(q: seq<int>,i:nat,t:Tree,i0:nat,t0:Tree)
	requires i>i0 && i==i0+1 && Inv(q,t,i)
	ensures V(q,i0) > V(q,i)
	ensures Inv(q,t,i) 
{}

predicate method Guard1(q: seq<int>,i:nat,t:Tree)
{
	i < |q|
}

method Init(q: seq<int>) returns (i: nat, t: Tree)
requires NoDuplicates(q)
ensures i==0
ensures t==Empty
ensures Inv(q,t,i)
{//assignment
	

	LemmaInit(q);

	i:=0;
	t:=Empty;


}

lemma LemmaInit(q: seq<int>) 
	requires NoDuplicates(q)
	ensures  Inv(q,Empty,0)
{}



method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
{


	match t0 {
		case Empty => t := Node(x, Empty, Empty);
		case Node(n',nt1,nt2) => 
			//alternation
			if(Guard2(x,n'))
			{

				

				LemmaBinarySearchSubtree(n',nt1,nt2);

				assert BST(nt1) && x !in NumbersInTree(nt1); //precondition of recursive call
				
				var tLeft := InsertBST(nt1, x);
				
				assert BST(tLeft) && NumbersInTree(tLeft) == NumbersInTree(nt1)+{x}; //postcondition of recursive call
				
				t := Node(n', tLeft, nt2);

				L_BST(n', nt1, nt2);
			
				L_greater(nt1, n', x, tLeft);

				assert NumbersInTree(t) == NumbersInTree(t0)+{x};
				assert BST(t);
			
			}
			else
			{

				LemmaBinarySearchSubtree(n',nt1,nt2);

				assert BST(nt2) && x !in NumbersInTree(nt2); //precondition of recursive call

				var tRight:Tree := InsertBST(nt2, x);

				assert BST(tRight) && NumbersInTree(tRight) == NumbersInTree(nt2)+{x}; //postcondition of recursive call

				t := Node(n', nt1, tRight);

				L_BST(n', nt1, nt2);
				
				L_smaller(nt2, n', x, tRight);

				assert NumbersInTree(t) == NumbersInTree(t0)+{x};
				assert BST(t);
				
			}
	}
	assert NumbersInTree(t) == NumbersInTree(t0)+{x}; 
	assert BST(t);
}



predicate method Guard2(x:int,n':int)
{
	x < n'
}

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


