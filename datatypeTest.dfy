datatype FoodTree = 
  Node(name: string, children: seq<FoodTree>)

datatype LabeledTree = 
  Labeled(name: string, labelName: string, children: seq<LabeledTree>)


method LabelTree(t: FoodTree, allergens: set<string>) returns (labelTree :LabeledTree)
    // requires false
    ensures true
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
}
function Pad(n: nat): string
  decreases n
{
  if n == 0 then "" else " " + Pad(n - 1)
}


method PrintLabeledTree(t: LabeledTree, indent: nat)
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

method Main()
{
  // Construct food tree
  var flour := Node("flour", []);
  var lactose := Node("lactose", []);
  var milk := Node("milk", [lactose]);
  var tortila := Node("tortila", [flour, milk]);
  var bread := Node("bread", [flour, tortila]);

  var chicken := Node("chicken", []);
  var letus := Node("letus", []);
  var tomato := Node("tomato", []);
  var salad := Node("salad", [letus, tomato]);

  var sandwich := Node("sandwich", [bread, chicken, salad]);

  var allergens := { "tortila", "tomato", "lactose"};

  var labeled := LabelTree(sandwich, allergens);

  PrintLabeledTree(labeled, 0);
}