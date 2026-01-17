datatype Node = Node(id: int, neighbors: seq<int>)

method GraphNodeVisit(nodes: array<Node>, start: int) returns (visited: set<int>)
  requires 0 <= start < nodes.Length
  ensures start in visited
  ensures forall x :: x in visited ==> 0 <= x < nodes.Length
{
  visited := {};
  var queue := [start];
  
  while |queue| > 0
    invariant forall x :: x in visited ==> 0 <= x < nodes.Length
    invariant forall x :: x in queue ==> 0 <= x < nodes.Length
  {
    var current := queue[0];
    queue := queue[1..];
    
    if current !in visited {
      visited := visited + {current};
      var i := 0;
      while i < |nodes[current].neighbors|
        invariant 0 <= i <= |nodes[current].neighbors|
      {
        var neighbor := nodes[current].neighbors[i];
        if neighbor !in visited {
          queue := queue + [neighbor];
        }
        i := i + 1;
      }
    }
  }
}
