datatype FoodTree =
  FoodNode(name: string, children: seq<FoodTree>)

datatype LabeledTree = 
  LabeledNode(name: string, labelname: string, children: seq<LabeledTree>)

predicate AllergenFree(t: FoodTree, allergens: set<string>) {
  match t case FoodNode(name, children) =>
    !(name in allergens) && forall child :: child in children ==> AllergenFree(child, allergens)
}

method LabelTree(t: FoodTree, allergens: set<string>) returns (lt: LabeledTree)
  ensures lt.labelname in {"safe", "not safe"}
  ensures lt.name == t.name
  ensures lt.labelname == "safe" <==> AllergenFree(t, allergens)
{
  var name := t.name;
  var children := t.children;

  var labeledChildren: seq<LabeledTree> := [];
  ghost var processedChildren: seq<FoodTree> := [];
  var anyUnsafe := false;

  if name in allergens {
    anyUnsafe := true;
    assert anyUnsafe == false <==> !(name in allergens);
  } else {
    var i := 0;
    while i < |children|
      invariant 0 <= i <= |children|
      invariant |labeledChildren| == |processedChildren| == i   
      invariant forall i :: 0 <= i < |processedChildren| ==> (processedChildren[i] == children[i])
      invariant anyUnsafe == false <==> (forall child :: child in processedChildren ==> AllergenFree(child, allergens))
      // these inviariants are not necessary for the proof but might be usefull:
      invariant forall labeledChild :: labeledChild in labeledChildren
                  ==> labeledChild.labelname in {"safe", "not safe"}
      invariant forall i: nat :: 0 < i < |processedChildren|
                  ==> labeledChildren[i].name == processedChildren[i].name
      decreases |children| - i
    {
      var child := children[i];
      var childLabeled := LabelTree(child, allergens);
      if childLabeled.labelname == "not safe" {
        anyUnsafe := true;
      }
      labeledChildren := labeledChildren + [childLabeled];
      processedChildren := processedChildren + [child];
      i := i + 1;
    }
    assert anyUnsafe == false <==> (forall child :: child in children ==> AllergenFree(child, allergens));
  }
  var labelN := if anyUnsafe then "not safe" else "safe";
  lt := LabeledNode(name, labelN, labeledChildren);
  assert lt.labelname == "safe" <==> !(name in allergens) && (forall child :: child in children ==> AllergenFree(child, allergens));
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