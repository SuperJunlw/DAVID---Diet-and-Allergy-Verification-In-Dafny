datatype FoodTree =
  Ingredient(name: string) |
  Choice(name: string, children: seq<FoodTree>)

datatype LabeledTree = 
  LabeledNode(name: string, labelname: string, children: seq<LabeledTree>)

predicate AllergenFree(t: FoodTree, allergens: set<string>) {
  match t
  case Ingredient(name) => !(name in allergens)
  case Choice(_, children) =>
    forall child :: child in children ==> AllergenFree(child, allergens)
}

method LabelTree(t: FoodTree, allergens: set<string>) returns (lt: LabeledTree)
  ensures lt.labelname in {"safe", "not safe"}
  ensures lt.name == t.name
  ensures lt.labelname == "safe" <==> AllergenFree(t, allergens)
{
  match t
  //label for leaf node (node doesn't have children)
  case Ingredient(name) =>
    if name in allergens {
      lt := LabeledNode(name, "not safe", []);
    } else {
      lt := LabeledNode(name, "safe", []);
    }

  //label for nodes that have children
  case Choice(name, children) =>
    var labeledChildren: seq<LabeledTree> := [];
    ghost var processedChildren: seq<FoodTree> := [];
    var anyUnsafe := false;

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
    var labelN := if anyUnsafe then "not safe" else "safe";
    lt := LabeledNode(name, labelN, labeledChildren);
    assert lt.labelname == "safe" <==> (forall child :: child in children ==> AllergenFree(child, allergens));
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
  var flour := Ingredient("flour");
  var lactose := Ingredient("lactose");
  var milk := Choice("milk", [lactose]);
  var tortila := Choice("tortila", [flour, milk]);
  var bread := Choice("bread", [flour, tortila]);

  var chicken := Ingredient("chicken");
  var letus := Ingredient("letus");
  var tomato := Ingredient("tomato");
  var salad := Choice("salad", [letus, tomato]);

  var sandwich := Choice("sandwich", [bread, chicken, salad]);

  var allergens := { "tortila", "tomato", "lactose" };

  var labeled := LabelTree(sandwich, allergens);

  PrintLabeledTree(labeled, 0);
}


