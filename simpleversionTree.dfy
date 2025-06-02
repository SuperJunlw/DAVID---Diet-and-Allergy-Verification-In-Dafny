datatype NodeType =
  Normal | Choice

datatype FoodTree =
  FoodNode(name: string, nodeType: NodeType, children: seq<FoodTree>)

datatype FoodLabel =
  Safe | Warning | Unsafe

datatype LabeledTree = 
  LabeledNode(name: string, labelname: FoodLabel, children: seq<LabeledTree>)

predicate AllSafe(t: FoodTree, allergens: set<string>) {
  // true if and only if the node is completely allergen free
  !(t.name in allergens) && forall child :: child in t.children ==> AllSafe(child, allergens)
}
predicate SomeSafe(t: FoodTree, allergens: set<string>) {
  // true if and only if there is at least one free option is allergy-compatible
  // (there is a path on the tree with branches at choice nodes where none
  //  of the ingredients are allergens)
  AllSafe(t, allergens) || (
  !(t.name in allergens) && 
  match t.nodeType
  case Normal =>
    // If the node is not a choice node, all children must have a allergen free option
    forall child :: child in t.children ==> SomeSafe(child, allergens)
  case Choice =>
    // If the node is a choice node, only one child must have an allergen free option
    |t.children| == 0 || exists child :: child in t.children && SomeSafe(child, allergens))
}

predicate IsSafe(t: FoodTree, allergens: set<string>) {
  // "safe" indicates that the node is completely allergen-free
  AllSafe(t, allergens) && SomeSafe(t, allergens)
  // Note that AllSafe ==> SomeSafe. However, this is easier to prove as a loop inviariant.
}
predicate IsWarning(t: FoodTree, allergens: set<string>) {
  // "warning" indicates the node has at least one allergen free option available
  // (but NOT ALL options are allergen free)
  SomeSafe(t, allergens) && !AllSafe(t, allergens)
}
predicate IsUnsafe(t: FoodTree, allergens: set<string>) {
  // "unsafe" indicates the node is guarenteed to contain the allergen
  // (i.e. all options contain the allergen)
  !SomeSafe(t, allergens) && !AllSafe(t, allergens)
}

lemma OneOfIsSafeIsWarningOrIsUnsafe(t: FoodTree, allergens: set<string>) returns (n: nat)
ensures n == 1
{
  // A node can be either safe, warning, or unsafe
  n := 0;
  if (IsSafe(t, allergens)) {
    n := n + 1;
  }
  if (IsWarning(t, allergens)) {
    n := n + 1;
  }
  if (IsUnsafe(t, allergens)) {
    n := n + 1;
  }
}

predicate NodeCorrect(t: FoodTree, lt: LabeledTree, allergens: set<string>) {
  // Check that for the root node in the label tree:
  // 1. Has a name that matches the original food tree
  lt.name == t.name &&
  // 2. The children's lengths are equivalent
  |lt.children| == |t.children| &&
  // 3. Label is correct
  (lt.labelname == Safe <==> IsSafe(t, allergens)) && 
  (lt.labelname == Warning <==> IsWarning(t, allergens)) &&
  (lt.labelname == Unsafe <==> IsUnsafe(t, allergens))
}

predicate AllNodesCorrect(t: FoodTree, lt: LabeledTree, allergens: set<string>)
{
  NodeCorrect(t, lt, allergens) &&
  // 4. All children are also correct (matching name/children lengths and correct label)
  forall i: nat :: 0 <= i < |t.children| ==> AllNodesCorrect(t.children[i], lt.children[i], allergens)
}

method LabelTree(t: FoodTree, allergens: set<string>) returns (lt: LabeledTree)
  ensures lt.name == t.name
  ensures |lt.children| == |t.children|
  ensures lt.labelname == Safe <==> IsSafe(t, allergens)
  ensures lt.labelname == Warning <==> IsWarning(t, allergens)
  ensures lt.labelname == Unsafe <==> IsUnsafe(t, allergens)
  ensures AllNodesCorrect(t, lt, allergens)
{
  var name := t.name;
  var children := t.children;

  var labeledChildren: seq<LabeledTree> := [];
  ghost var processedChildren: seq<FoodTree> := [];

  var isAllergen := name in allergens;
  var noChildren := |children| == 0;

  // Initialize basebases
  var existsSomeSafe := false;
  var allSomeSafe := true;
  var allSafe := true;
  var i := 0;
  while i < |children|
    invariant 0 <= i <= |children|
    invariant |labeledChildren| == |processedChildren| == i
    invariant forall i: nat :: 0 <= i < |processedChildren| ==> processedChildren[i] == children[i]
    invariant forall i: nat :: 0 < i < |processedChildren| ==> labeledChildren[i].name == processedChildren[i].name
    invariant forall i: nat :: 0 <= i < |processedChildren| ==> AllNodesCorrect(processedChildren[i], labeledChildren[i], allergens)    
    invariant existsSomeSafe <==> exists i: nat :: 0 <= i < |processedChildren| && SomeSafe(processedChildren[i], allergens)
    invariant allSomeSafe <==> forall i: nat :: 0 <= i < |processedChildren| ==> SomeSafe(processedChildren[i], allergens)
    invariant allSafe <==> forall i: nat :: 0 <= i < |processedChildren| ==> AllSafe(processedChildren[i], allergens)
    invariant allSafe ==> allSomeSafe
    decreases |children| - i
  {
    var child := children[i];
    var childLabeled := LabelTree(child, allergens);
    assert NodeCorrect(child, childLabeled, allergens);
    if childLabeled.labelname == Safe {
      assert SomeSafe(child, allergens);
      assert AllSafe(child, allergens);
      existsSomeSafe := true;
    } else if childLabeled.labelname == Warning {
      assert SomeSafe(child, allergens);
      assert !AllSafe(child, allergens);
      existsSomeSafe := true;
      allSafe := false;
    } else {
      assert childLabeled.labelname == Unsafe;
      assert !SomeSafe(child, allergens);
      assert !AllSafe(child, allergens);
      allSafe := false;
      allSomeSafe := false;
    }
    labeledChildren := labeledChildren + [childLabeled];
    processedChildren := processedChildren + [child];
    i := i + 1;
  }
  assert children == processedChildren;
  assert existsSomeSafe <==> exists child :: child in children && SomeSafe(child, allergens);
  assert allSomeSafe <==> forall child :: child in children ==> SomeSafe(child, allergens);
  assert allSafe <==> forall child :: child in children ==> AllSafe(child, allergens);
  
  ghost var fullAllSafe := !isAllergen && allSafe;
  ghost var fullSomeSafe := fullAllSafe || ( !isAllergen && match t.nodeType
            case Normal => allSomeSafe
            case Choice => noChildren || existsSomeSafe );
  assert fullAllSafe <==> AllSafe(t, allergens);
  assert fullSomeSafe <==> SomeSafe(t, allergens);
  
  ghost var isSafe := fullAllSafe && fullSomeSafe;
  ghost var isWarning := fullSomeSafe && !fullAllSafe;
  ghost var isUnsafe := !fullSomeSafe && !fullAllSafe;
  assert isWarning <==> IsWarning(t, allergens);
  assert isSafe <==> IsSafe(t, allergens);
  assert isUnsafe <==> IsUnsafe(t, allergens);

  var labelN :=
    if isAllergen then
      Unsafe
    else if allSafe then
      Safe
    else if (match t.nodeType
             case Normal => allSomeSafe
             case Choice => noChildren || existsSomeSafe) then
      Warning
    else
      Unsafe;

  assert labelN == Safe <==> isSafe;
  assert labelN == Warning <==> isWarning;
  assert labelN == Unsafe <==> isUnsafe;

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
  var labelStr := match t.labelname
    case Safe => "Safe"
    case Warning => "Warning: Some options are unsafe"
    case Unsafe => "Unsafe";
  print pad + t.name + " (" + labelStr + ")" + "\n";
  var i := 0;
  while i < |t.children|
    decreases |t.children| - i
  {
    PrintLabeledTree(t.children[i], indent + 2);
    i := i + 1;
  }
}

function Ingredient(name: string): FoodTree {
  FoodNode(name, Normal, [])
}

function Recipe(name: string, children: seq<FoodTree>): FoodTree {
  FoodNode(name, Normal, children)
}

function ChooseOne(name: string, children: seq<FoodTree>): FoodTree {
  FoodNode(name + " (choose one)", Choice, children)
}

method Main()
{
  var flour := Ingredient("flour");
  var lactose := Ingredient("lactose");
  var milk := Recipe("milk", [lactose]);
  var tortila := Recipe("tortila", [flour, milk]);
  var bread := Recipe("bread", [flour, tortila]);

  var chicken := Ingredient("chicken");
  var ham := Ingredient("ham");
  var protein := ChooseOne("Protein Topping", [chicken, ham]);

  var letus := Ingredient("letus");
  var tomato := Ingredient("tomato");
  var salad := Recipe("salad", [letus, tomato]);

  var sandwich := Recipe("sandwich", [bread, protein, salad]);

  var allergens := { "tortila", "tomato", "lactose", "ham"};

  var labeled := LabelTree(sandwich, allergens);

  PrintLabeledTree(labeled, 0);
}