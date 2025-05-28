method CompareTwoList(ingredients: seq<string>, allergens: set<string>) returns (isSafe: bool)
    requires |ingredients| >= 0
    ensures |ingredients| == 0 ==> isSafe
    ensures |allergens| == 0 ==> isSafe //if nothing in the allergen list, then isSafe must be true
    //if isSafe is true, then none of the ingredients are in the allergens list, and vice versa
    ensures isSafe <==> forall ing :: ing in ingredients ==> ing !in allergens
    //if isSafe is false, then there exist a ingredient in both ingredient list and allergen list
    ensures !isSafe ==> exists ing :: ing in ingredients && ing in allergens
{
    var i := 0;
    isSafe := true;

    while i < |ingredients|
    invariant 0 <= i <= |ingredients|
    //if isSafe is true so far, then all the ingredients checked so far are in the allergen list
    invariant isSafe ==> forall j :: 0 <= j < i ==> ingredients[j] !in allergens
    decreases |ingredients| - i //loop is guaranteed to terminate
  {
    if ingredients[i] in allergens {
      isSafe := false;
      return;
    }
    i := i + 1;
  }
}

method TestMethod()
{
  var ingredients1 := ["apple", "banana", "carrot"];
  var allergens1 := {"peanut", "shellfish"};
  var result1 := CompareTwoList(ingredients1, allergens1);
  assert result1; // should be true 

  var ingredients2 := ["milk", "egg", "peanut"];
  var allergens2 := {"peanut", "gluten"};
  var result2 := CompareTwoList(ingredients2, allergens2);
  assert !result2; // should be false 

  var ingredients3 := [];
  var allergens3 := {"soy"};
  var result3 := CompareTwoList(ingredients3, allergens3);
  assert result3; // should be true 

  var ingredients4 := ["egg"];
  var allergens4 := {};
  var result4 := CompareTwoList(ingredients4, allergens4);
  assert result4; // should be true 
}