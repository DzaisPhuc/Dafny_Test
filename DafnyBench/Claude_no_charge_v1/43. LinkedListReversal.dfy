class Node {
  var data: int
  var next: Node?
}

method LinkedListReversal(head: Node?) returns (newHead: Node?)
  modifies set n | n in Nodes(head) :: n
  ensures newHead != null ==> newHead in Nodes(old(head))
{
  var prev: Node? := null;
  var current := head;
  
  while current != null
    invariant current == null || current in Nodes(old(head))
    decreases Nodes(current)
  {
    var nextNode := current.next;
    current.next := prev;
    prev := current;
    current := nextNode;
  }
  
  newHead := prev;
}

function Nodes(n: Node?): set<Node>
  reads set x | x in Reachable(n) :: x
{
  if n == null then {} else {n} + Nodes(n.next)
}

function Reachable(n: Node?): set<Node>
  reads set x | x in ReachableHelper(n, {}) :: x
{
  ReachableHelper(n, {})
}

function ReachableHelper(n: Node?, visited: set<Node>): set<Node>
  reads set x | x !in visited && (n != null ==> x in Reachable(n.next)) :: x
{
  if n == null || n in visited then visited
  else ReachableHelper(n.next, visited + {n})
}
