datatype FoodTree = 
  Node(name: string, children: seq<FoodTree>)

datatype LabeledTree = 
  Labeled(name: string, labelName: string, children: seq<LabeledTree>)

//TODO: NOT working these lemmas either
// lemma SafeLabelCorrectness(t: FoodTree, allergens: set<string>, labeledTree: LabeledTree)
//     ensures (labeledTree.labelName == "safe" ==> !(labeledTree.name in allergens))
// {
//   // If the node is labeled "safe", its name must not be in allergens.
//   if labeledTree.labelName == "safe" {
//     assert !(labeledTree.name in allergens); // Ensure the name is not in allergens
//   }
// }

// lemma SafeChildren(t: FoodTree, allergens: set<string>, labeledTree: LabeledTree)
//     ensures (labeledTree.labelName == "safe" ==> (forall i: int :: 0 <= i < |labeledTree.children| ==> labeledTree.children[i].labelName == "safe"))
// {
//   if labeledTree.labelName == "safe" {
//     // Check that all children are labeled "safe"
//     forall i: int :: 0 <= i < |labeledTree.children| ==> labeledTree.children[i].labelName == "safe";
//   }
// }

method LabelTree(t: FoodTree, allergens: set<string>) returns (labelTree :LabeledTree)
    // requires false
    // ensures true
    // ensures forall n: LabeledTree :: n in labelTree.children ==> (n.labelName == "safe" ==> !(n.name in allergens))
    // ensures (labelTree.labelName == "safe" ==> forall c: LabeledTree :: c in labelTree.children ==> c.labelName == "safe")
    ensures (labelTree.labelName == "safe" ==> !(labelTree.name in allergens))
    ensures (labelTree.labelName == "not safe" ==> (labelTree.name in allergens || exists c: LabeledTree :: c in labelTree.children && c.labelName == "not safe"))
{
  var labeledChildren: seq<LabeledTree> := [];
  var i := 0;
  while i < |t.children|
    invariant 0 <= i <= |t.children|
    invariant |labeledChildren| == i
    decreases |t.children| - i
  {
    var childLabel := LabelTree(t.children[i], allergens);
    labeledChildren := labeledChildren + [childLabel];
    i := i + 1;
  }

  var unsafe := t.name in allergens || exists j :: 0 <= j < |labeledChildren| && labeledChildren[j].labelName == "not safe";
  var labelName := if unsafe then "not safe" else "safe";
  labelTree := Labeled(t.name, labelName, labeledChildren);

   // Ensure that if the node is labeled "safe", then it is not in the allergens set
  // if labelTree.labelName == "safe" {
  //   // We ensure that "safe" nodes are not in allergens by adding this invariant
  //   assert !(labelTree.name in allergens);  // This ensures consistency during labeling
  // }

  //TODO: not working this below part
  // Use a while loop to check that all children that are labeled "safe" are not in allergens
  // var j := 0;
  // while j < |labeledChildren|
  //   invariant 0 <= j <= |labeledChildren|
  //   decreases |labeledChildren| - j
  // {
  // // Check if there is at least one child labeled "not safe" that is in the allergens list
  // if labeledChildren[j].labelName == "not safe" {
  //   assert exists c: LabeledTree :: c in labeledChildren && c.name in allergens;
  // }
  // j := j + 1;
  // }
}
function Pad(n: nat): string
  decreases n
{
  if n == 0 then "" else " " + Pad(n - 1)
}


method PrintLabeledTree(t: LabeledTree, indent: nat)
    // ensures t.labelName == "safe" ==> !(t.name in allergens)
    // ensures t.labelName == "not safe" ==> (t.name in allergens || exists c: LabeledTree :: c.labelName == "not safe")
{
  var pad := Pad(indent);
  print pad + t.name + " (" + t.labelName + ")\n";
  var i := 0;
  while i < |t.children|
    decreases |t.children| - i
  {
    PrintLabeledTree(t.children[i], indent + 2);
    i := i + 1;
  }
}

// invariant allSafe ==> allSomeSafe
// decreases |children| - i
// method Main()
// {
//   // Construct food tree
//   var flour := Node("flour", []);
//   var lactose := Node("lactose", []);
//   var milk := Node("milk", [lactose]);
//   var tortila := Node("tortila", [flour, milk]);
//   var bread := Node("bread", [flour, tortila]);

//   var chicken := Node("chicken", []);
//   var letus := Node("letus", []);
//   var tomato := Node("tomato", []);
//   var salad := Node("salad", [letus, tomato]);

//   var sandwich := Node("sandwich", [bread, chicken, salad]);

//   var allergens := { "tortila", "tomato", "lactose"};

//   var labeled := LabelTree(sandwich, allergens);
//   assert labeled.labelName == "not safe";

//   PrintLabeledTree(labeled, 0);
// }