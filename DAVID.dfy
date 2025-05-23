// Tree structure to represent menu items and subchoices

datatype NodeType = Leaf | ChoiceGroup

datatype MenuTree =
  IngredientNode(name: string, isAllergen: bool) // Leaf node
| Choice(labelName: string, options: seq<MenuTree>)  // Internal node

// Label for allergen safety
datatype AllergyLabel = Safe | Warning | Unsafe

// Function to check if a leaf is unsafe
function isUnsafe(node: MenuTree, allergens: set<string>): bool
{
  match node
  case IngredientNode(name, isAllergen) =>
    isAllergen && name in allergens
  case Choice(_, _) =>
    false
}

// Recursively annotate tree for allergen safety
ghost function annotateTree(node: MenuTree, allergens: set<string>): AllergyLabel
{
  match node
  case IngredientNode(name, isAllergen) =>
    if isAllergen && name in allergens then Unsafe else Safe

  case Choice(_, options) =>
    if forall i :: 0 <= i < |options| ==> annotateTree(options[i], allergens) == Unsafe then
      Unsafe
    else if exists i :: 0 <= i < |options| && annotateTree(options[i], allergens) == Unsafe then
      Warning
    else
      Safe
}

// Specification: menu item containing allergens must not be labeled safe
method verifyUnsafeTreeNotSafe(tree: MenuTree, allergens: set<string>)
  requires exists ing :: ing in allergens && containsAllergen(tree, ing)
  ensures annotateTree(tree, allergens) != Safe
{
}

// Helper: recursively check tree for allergen presence
ghost function containsAllergen(tree: MenuTree, allergen: string): bool
{
  match tree
  case IngredientNode(name, isAllergen) =>
    isAllergen && name == allergen

  case Choice(_, options) =>
    exists i :: 0 <= i < |options| && containsAllergen(options[i], allergen)
}
