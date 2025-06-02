datatype FoodTree =
  FoodNode(name: string, children: seq<FoodTree>)

datatype LabeledTree = 
  LabeledNode(name: string, labelname: string, children: seq<LabeledTree>)

predicate AllergenFree(t: FoodTree, allergens: set<string>) {
  !(t.name in allergens) && forall child :: child in t.children ==> AllergenFree(child, allergens)
}

predicate AllNodesCorrect(t: FoodTree, lt: LabeledTree, allergens: set<string>)
{
  // Check that for all nodes in the label tree:
  // 1. Has a name that match the original food tree
  lt.name == t.name &&
  // 2. Label is correct ("safe" indicates the node is alergen free)
  (lt.labelname == "safe" <==> AllergenFree(t, allergens)) &&
  // 3. The children's lengths are equivalent
  |lt.children| == |t.children| &&
  // 4. All children are also correct
  forall i: nat :: 0 <= i < |t.children| ==> AllNodesCorrect(t.children[i], lt.children[i], allergens)
}

method LabelTree(t: FoodTree, allergens: set<string>) returns (lt: LabeledTree)
  ensures lt.name == t.name
  ensures |lt.children| == |t.children|
  ensures lt.labelname in {"safe", "not safe"}
  ensures AllNodesCorrect(t, lt, allergens)
{
  var name := t.name;
  var children := t.children;

  var labeledChildren: seq<LabeledTree> := [];
  ghost var processedChildren: seq<FoodTree> := [];
  var anyUnsafe := false;

  if name in allergens {
    anyUnsafe := true;
  }
  var i := 0;
  while i < |children|
    invariant 0 <= i <= |children|
    invariant |labeledChildren| == |processedChildren| == i
    invariant forall i: nat :: 0 <= i < |processedChildren| ==> processedChildren[i] == children[i]
    invariant forall i: nat :: 0 < i < |processedChildren| ==> labeledChildren[i].name == processedChildren[i].name
    invariant forall i: nat :: 0 <= i < |processedChildren| ==> AllNodesCorrect(processedChildren[i], labeledChildren[i], allergens)    
    invariant !anyUnsafe <==> !(name in allergens) && forall child :: child in processedChildren ==> AllergenFree(child, allergens)
    decreases |children| - i
  {
    var child := children[i];
    var childLabeled := LabelTree(child, allergens);
    assert childLabeled.labelname == "safe" <==> AllergenFree(child, allergens);
    if childLabeled.labelname == "not safe" {
      anyUnsafe := true;
    }
    labeledChildren := labeledChildren + [childLabeled];
    processedChildren := processedChildren + [child];
    i := i + 1;
  }
  assert anyUnsafe <==> name in allergens || !(forall child :: child in processedChildren ==> AllergenFree(child, allergens));
  assert anyUnsafe <==> !AllergenFree(t, allergens);
  var labelN := if anyUnsafe then "not safe" else "safe";
  lt := LabeledNode(name, labelN, labeledChildren);
}

function Pad(n: nat): string
  decreases n
{
  if n == 0 then "" else " " + Pad(n - 1)
}

method PrintLabeledTree(t: LabeledTree, indent: nat)
{
  var pad := Pad(indent);
  print pad + t.name + " (" + t.labelname + ")\n";
  var i := 0;
  while i < |t.children|
    decreases |t.children| - i
  {
    PrintLabeledTree(t.children[i], indent + 2);
    i := i + 1;
  }
}

method Main()
{
  var flour := FoodNode("flour", []);
  var lactose := FoodNode("lactose", []);
  var milk := FoodNode("milk", [lactose]);
  var tortila := FoodNode("tortila", [flour, milk]);
  var bread := FoodNode("bread", [flour, tortila]);

  var chicken := FoodNode("chicken", []);
  var letus := FoodNode("letus", []);
  var tomato := FoodNode("tomato", []);
  var salad := FoodNode("salad", [letus, tomato]);

  var sandwich := FoodNode("sandwich", [bread, chicken, salad]);

  var allergens := { "tortila", "tomato", "lactose" };

  var labeled := LabelTree(sandwich, allergens);

  PrintLabeledTree(labeled, 0);
}