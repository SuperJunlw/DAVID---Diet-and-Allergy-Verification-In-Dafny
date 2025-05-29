datatype FoodTree =
  Ingredient(name: string) |
  Choice(name: string, children: seq<FoodTree>)

datatype LabeledTree = 
  LabeledNode(name: string, labelname: string, children: seq<LabeledTree>)

function IsIngredientSafe(name: string, allergens: set<string>): bool
{
  name !in allergens
}

function AllIngredients(t: FoodTree): set<string>
{
  match t
  case Ingredient(name) => {name}
  case Choice(_, children) =>
    set ing | c := children[..], i :: 0 <= i < |children|, ing in AllIngredients(children[i]) :: true
}

method LabelTree(t: FoodTree, allergens: set<string>) returns (lt: LabeledTree)
  ensures lt.labelname == "safe" <==> (t.AllIngredients(t) * allergens) == {}
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
    var anyUnsafe := false;

    var i := 0;
    while i < |children|
      invariant 0 <= i <= |children|
      invariant |labeledChildren| == i
      decreases |children| - i
    {
      var childLabeled := LabelTree(children[i], allergens);
      if childLabeled.labelname == "not safe" {
        anyUnsafe := true;
      }
      labeledChildren := labeledChildren + [childLabeled];
      i := i + 1;
    }

    var labelN := if anyUnsafe then "not safe" else "safe";
    lt := LabeledNode(name, labelN, labeledChildren);
}

