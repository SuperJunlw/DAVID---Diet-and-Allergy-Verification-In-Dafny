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
      assert t == Ingredient(name);
      assert !(name in allergens);
      assert AllergenFree(t, allergens);
    }

  //label for nodes that have children
  case Choice(name, children) =>
    var labeledChildren: seq<LabeledTree> := [];
    ghost var processedChildren: seq<FoodTree> := [];
    var anyUnsafe := false;

    var i := 0;
    while i < |children|
      invariant 0 <= i <= |children|
      invariant |labeledChildren| == i
      invariant forall labeledChild :: labeledChild in labeledChildren
                  ==> labeledChild.labelname in {"safe", "not safe"}
      invariant |labeledChildren| == |processedChildren|
      invariant forall i: nat :: 0 < i < |processedChildren|
                  ==> labeledChildren[i].name == processedChildren[i].name
      invariant forall i :: 0 <= i < |processedChildren|
                  ==> (labeledChildren[i].labelname == "not safe" <==> !AllergenFree(processedChildren[i], allergens))
      invariant forall i :: 0 <= i < |processedChildren|
                  ==> (processedChildren[i] == children[i])
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
    assert |processedChildren| == |children|;
    assert forall i :: 0 <= i < |children|
                  ==> (processedChildren[i] == children[i]);
    assert processedChildren == children;
    assert forall i :: 0 <= i < |children|
            ==> (labeledChildren[i].labelname == "not safe" <==> !AllergenFree(processedChildren[i], allergens));

    var labelN := if anyUnsafe then "not safe" else "safe";
    lt := LabeledNode(name, labelN, labeledChildren);
}

