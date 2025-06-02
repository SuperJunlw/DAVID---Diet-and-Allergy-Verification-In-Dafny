datatype NodeType =
  Normal | Choice

datatype FoodTree =
  FoodNode(name: string, nodeType: NodeType, children: seq<FoodTree>)

datatype FoodLabel =
  Safe | Warning | Unsafe

datatype LabeledTree = 
  LabeledNode(name: string, labelname: FoodLabel, children: seq<LabeledTree>)

predicate IsSafe(t: FoodTree, allergens: set<string>) {
  // "safe" indicates that the node is completely allergen-free
  AllSafe(t, allergens) && SomeSafe(t, allergens)
}
predicate IsWarning(t: FoodTree, allergens: set<string>) {
  // "warning" indicates the node has allergen free options available (but not all options are allergen tree)
  SomeSafe(t, allergens) && !AllSafe(t, allergens)
}
predicate IsUnsafe(t: FoodTree, allergens: set<string>) {
  // "unsafe" idicates the node is guarenteed to contain the allergen (all options contain the allergen)
  !SomeSafe(t, allergens) && !AllSafe(t, allergens)
}

predicate AllSafe(t: FoodTree, allergens: set<string>) {
  !(t.name in allergens) && forall child :: child in t.children ==> AllSafe(child, allergens)
}
predicate SomeSafe(t: FoodTree, allergens: set<string>) {
  AllSafe(t, allergens) || (
  !(t.name in allergens) && 
  match t.nodeType
  case Normal =>
    forall child :: child in t.children ==> SomeSafe(child, allergens)
  case Choice =>
    // Check to see if at least one option is safe
    |t.children| == 0 || exists child :: child in t.children && SomeSafe(child, allergens))
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
  //ensures AllNodesCorrect(t, lt, allergens)
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
  assert allSafe == allSomeSafe;
  var i := 0;
  while i < |children|
    invariant 0 <= i <= |children|
    invariant |labeledChildren| == |processedChildren| == i
    invariant forall i: nat :: 0 <= i < |processedChildren| ==> processedChildren[i] == children[i]
    invariant forall i: nat :: 0 < i < |processedChildren| ==> labeledChildren[i].name == processedChildren[i].name
    //invariant forall i: nat :: 0 <= i < |processedChildren| ==> AllNodesCorrect(processedChildren[i], labeledChildren[i], allergens)    
    invariant existsSomeSafe <==> exists child :: child in processedChildren && SomeSafe(child, allergens)
    invariant allSomeSafe <==> forall child :: child in processedChildren ==> SomeSafe(child, allergens)
    invariant allSafe <==> forall child :: child in processedChildren ==> AllSafe(child, allergens)
    invariant allSafe ==> allSomeSafe
    decreases |children| - i
  {
    var child := children[i];
    var childLabeled := LabelTree(child, allergens);
    assert NodeCorrect(child, childLabeled, allergens);
    if childLabeled.labelname == Unsafe {
      assert !SomeSafe(child, allergens);
      assert !AllSafe(child, allergens);
      allSafe := false;
      allSomeSafe := false;
    } else if childLabeled.labelname == Warning {
      assert SomeSafe(child, allergens);
      assert !AllSafe(child, allergens);
      existsSomeSafe := true;
      allSafe := false;
    } else {
      assert childLabeled.labelname == Safe;
      assert SomeSafe(child, allergens);
      assert AllSafe(child, allergens);
      existsSomeSafe := true;
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