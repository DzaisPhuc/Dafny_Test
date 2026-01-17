class TreeNode {
  var data: int
  var left: TreeNode?
  var right: TreeNode?
}

method BSTInsertion(root: TreeNode?, value: int) returns (newRoot: TreeNode?)
  ensures newRoot != null
  ensures newRoot.data == value || (root != null && newRoot == root)
{
  if root == null {
    newRoot := new TreeNode;
    newRoot.data := value;
    newRoot.left := null;
    newRoot.right := null;
  } else {
    if value < root.data {
      if root.left == null {
        var newNode := new TreeNode;
        newNode.data := value;
        newNode.left := null;
        newNode.right := null;
        root.left := newNode;
      } else {
        var _ := BSTInsertion(root.left, value);
      }
    } else if value > root.data {
      if root.right == null {
        var newNode := new TreeNode;
        newNode.data := value;
        newNode.left := null;
        newNode.right := null;
        root.right := newNode;
      } else {
        var _ := BSTInsertion(root.right, value);
      }
    }
    newRoot := root;
  }
}
