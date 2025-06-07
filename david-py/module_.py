import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: module_

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def IsAllergen(t, allergens):
        return ((t).isIngredient) and (((t).name) in (allergens))

    @staticmethod
    def AllSafe(t, allergens):
        def lambda0_(forall_var_0_):
            d_0_child_: FoodTree = forall_var_0_
            return not ((d_0_child_) in ((t).children)) or (default__.AllSafe(d_0_child_, allergens))

        return (not(default__.IsAllergen(t, allergens))) and (_dafny.quantifier(((t).children).UniqueElements, True, lambda0_))

    @staticmethod
    def SomeSafe(t, allergens):
        def lambda0_():
            source0_ = (t).nodeType
            if True:
                if source0_.is_Normal:
                    def lambda1_(forall_var_0_):
                        d_0_child_: FoodTree = forall_var_0_
                        return not ((d_0_child_) in ((t).children)) or (default__.SomeSafe(d_0_child_, allergens))

                    return _dafny.quantifier(((t).children).UniqueElements, True, lambda1_)
            if True:
                def lambda2_(exists_var_0_):
                    d_1_child_: FoodTree = exists_var_0_
                    return ((d_1_child_) in ((t).children)) and (default__.SomeSafe(d_1_child_, allergens))

                return ((len((t).children)) == (0)) or (_dafny.quantifier(((t).children).UniqueElements, False, lambda2_))

        return (default__.AllSafe(t, allergens)) or ((not(default__.IsAllergen(t, allergens))) and (lambda0_()))

    @staticmethod
    def IsSafe(t, allergens):
        return default__.AllSafe(t, allergens)

    @staticmethod
    def IsWarning(t, allergens):
        return (default__.SomeSafe(t, allergens)) and (not(default__.AllSafe(t, allergens)))

    @staticmethod
    def IsUnsafe(t, allergens):
        return not(default__.SomeSafe(t, allergens))

    @staticmethod
    def AllNodesCorrect(t, lt, allergens):
        def lambda0_(forall_var_0_):
            d_0_i_: int = forall_var_0_
            if System_.nat._Is(d_0_i_):
                return not (((0) <= (d_0_i_)) and ((d_0_i_) < (len((t).children)))) or (default__.AllNodesCorrect(((t).children)[d_0_i_], ((lt).children)[d_0_i_], allergens))
            elif True:
                return True

        return (((((((lt).name) == ((t).name)) and ((len((lt).children)) == (len((t).children)))) and ((((lt).labelname) == (FoodLabel_Safe())) == (default__.IsSafe(t, allergens)))) and ((((lt).labelname) == (FoodLabel_Warning())) == (default__.IsWarning(t, allergens)))) and ((((lt).labelname) == (FoodLabel_Unsafe())) == (default__.IsUnsafe(t, allergens)))) and (_dafny.quantifier(_dafny.IntegerRange(0, len((t).children)), True, lambda0_))

    @staticmethod
    def LabelTree(t, allergens):
        lt: LabeledTree = LabeledTree.default()()
        d_0_name_: _dafny.Seq
        d_0_name_ = (t).name
        d_1_children_: _dafny.Seq
        d_1_children_ = (t).children
        d_2_isIngredient_: bool
        d_2_isIngredient_ = (t).isIngredient
        d_3_labeledChildren_: _dafny.Seq
        d_3_labeledChildren_ = _dafny.SeqWithoutIsStrInference([])
        d_4_isAllergen_: bool
        d_4_isAllergen_ = (d_2_isIngredient_) and ((d_0_name_) in (allergens))
        d_5_noChildren_: bool
        d_5_noChildren_ = (len(d_1_children_)) == (0)
        d_6_existsSomeSafe_: bool
        d_6_existsSomeSafe_ = False
        d_7_allSomeSafe_: bool
        d_7_allSomeSafe_ = True
        d_8_allSafe_: bool
        d_8_allSafe_ = True
        d_9_i_: int
        d_9_i_ = 0
        while (d_9_i_) < (len(d_1_children_)):
            d_10_child_: FoodTree
            d_10_child_ = (d_1_children_)[d_9_i_]
            d_11_childLabeled_: LabeledTree
            out0_: LabeledTree
            out0_ = default__.LabelTree(d_10_child_, allergens)
            d_11_childLabeled_ = out0_
            if ((d_11_childLabeled_).labelname) == (FoodLabel_Safe()):
                d_6_existsSomeSafe_ = True
            elif ((d_11_childLabeled_).labelname) == (FoodLabel_Warning()):
                d_6_existsSomeSafe_ = True
                d_8_allSafe_ = False
            elif True:
                d_8_allSafe_ = False
                d_7_allSomeSafe_ = False
            d_3_labeledChildren_ = (d_3_labeledChildren_) + (_dafny.SeqWithoutIsStrInference([d_11_childLabeled_]))
            d_9_i_ = (d_9_i_) + (1)
        d_12_labelN_: FoodLabel
        def lambda0_():
            source0_ = (t).nodeType
            if True:
                if source0_.is_Normal:
                    return d_7_allSomeSafe_
            if True:
                return (d_5_noChildren_) or (d_6_existsSomeSafe_)

        if d_4_isAllergen_:
            d_12_labelN_ = FoodLabel_Unsafe()
        elif d_8_allSafe_:
            d_12_labelN_ = FoodLabel_Safe()
        elif lambda0_():
            d_12_labelN_ = FoodLabel_Warning()
        elif True:
            d_12_labelN_ = FoodLabel_Unsafe()
        lt = LabeledTree_LabeledNode(d_0_name_, d_12_labelN_, d_3_labeledChildren_)
        return lt

    @staticmethod
    def Pad(n):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (n) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))
                    in0_ = (n) - (1)
                    n = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PrintLabeledTree(t, indent):
        d_0_pad_: _dafny.Seq
        d_0_pad_ = default__.Pad(indent)
        d_1_labelStr_: _dafny.Seq
        source0_ = (t).labelname
        with _dafny.label("match0"):
            if True:
                if source0_.is_Safe:
                    d_1_labelStr_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Safe"))
                    raise _dafny.Break("match0")
            if True:
                if source0_.is_Warning:
                    d_1_labelStr_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Warning: Some options are unsafe"))
                    raise _dafny.Break("match0")
            if True:
                d_1_labelStr_ = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Unsafe"))
            pass
        _dafny.print(((((((d_0_pad_) + ((t).name)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " (")))) + (d_1_labelStr_)) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")")))) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")))).VerbatimString(False))
        d_2_i_: int
        d_2_i_ = 0
        while (d_2_i_) < (len((t).children)):
            default__.PrintLabeledTree(((t).children)[d_2_i_], (indent) + (2))
            d_2_i_ = (d_2_i_) + (1)

    @staticmethod
    def Display(t, allergens):
        d_0_i_: int
        d_0_i_ = 0
        d_1_allergenSet_: _dafny.Set
        d_1_allergenSet_ = _dafny.Set({})
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Allergens: "))).VerbatimString(False))
        while (d_0_i_) < (len(allergens)):
            _dafny.print((((allergens)[d_0_i_]) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))).VerbatimString(False))
            d_1_allergenSet_ = (d_1_allergenSet_) | (_dafny.Set({(allergens)[d_0_i_]}))
            d_0_i_ = (d_0_i_) + (1)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n===================\n"))).VerbatimString(False))
        d_2_labeledTree_: LabeledTree
        out0_: LabeledTree
        out0_ = default__.LabelTree(t, d_1_allergenSet_)
        d_2_labeledTree_ = out0_
        default__.PrintLabeledTree(d_2_labeledTree_, 0)

    @staticmethod
    def Ingredient(name):
        return FoodTree_FoodNode(name, True, NodeType_Normal(), _dafny.SeqWithoutIsStrInference([]))

    @staticmethod
    def IngredientWithSubingredients(name, subingredients):
        return FoodTree_FoodNode(name, True, NodeType_Normal(), subingredients)

    @staticmethod
    def Dish(name, ingredients):
        return FoodTree_FoodNode(name, False, NodeType_Normal(), ingredients)

    @staticmethod
    def ChooseOne(name, children):
        return FoodTree_FoodNode((name) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " (choose one)"))), False, NodeType_Choice(), children)

    @staticmethod
    def Optional(option):
        return FoodTree_FoodNode(((option).name) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " (optional)"))), False, NodeType_Choice(), _dafny.SeqWithoutIsStrInference([FoodTree_FoodNode((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "No "))) + ((option).name), False, NodeType_Normal(), _dafny.SeqWithoutIsStrInference([])), option]))

    @staticmethod
    def Main(noArgsParameter__):
        updated_main_from_file(default__)
        # d_0_flour_: FoodTree
        # d_0_flour_ = default__.Ingredient(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "flour")))
        # d_1_lactose_: FoodTree
        # d_1_lactose_ = default__.Ingredient(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lactose")))
        # d_2_milk_: FoodTree
        # d_2_milk_ = default__.IngredientWithSubingredients(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "milk")), _dafny.SeqWithoutIsStrInference([d_1_lactose_]))
        # d_3_dough_: FoodTree
        # d_3_dough_ = default__.IngredientWithSubingredients(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "dough")), _dafny.SeqWithoutIsStrInference([d_0_flour_, d_2_milk_]))
        # d_4_bread_: FoodTree
        # d_4_bread_ = default__.IngredientWithSubingredients(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "bread")), _dafny.SeqWithoutIsStrInference([d_0_flour_, d_3_dough_]))
        # d_5_chicken_: FoodTree
        # d_5_chicken_ = default__.Ingredient(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "chicken")))
        # d_6_ham_: FoodTree
        # d_6_ham_ = default__.Ingredient(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ham")))
        # d_7_protein_: FoodTree
        # d_7_protein_ = default__.ChooseOne(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "Protein Topping")), _dafny.SeqWithoutIsStrInference([d_5_chicken_, d_6_ham_]))
        # d_8_letus_: FoodTree
        # d_8_letus_ = default__.Ingredient(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "letus")))
        # d_9_tomato_: FoodTree
        # d_9_tomato_ = default__.Ingredient(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tomato")))
        # d_10_salad_: FoodTree
        # d_10_salad_ = default__.IngredientWithSubingredients(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "salad")), _dafny.SeqWithoutIsStrInference([d_8_letus_, d_9_tomato_]))
        # d_11_ketchup_: FoodTree
        # d_11_ketchup_ = default__.IngredientWithSubingredients(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ketchup")), _dafny.SeqWithoutIsStrInference([d_9_tomato_]))
        # d_12_optionalKetchup_: FoodTree
        # d_12_optionalKetchup_ = default__.Optional(d_11_ketchup_)
        # d_13_sandwich_: FoodTree
        # d_13_sandwich_ = default__.Dish(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "sandwich")), _dafny.SeqWithoutIsStrInference([d_4_bread_, d_7_protein_, d_10_salad_, d_12_optionalKetchup_]))
        # default__.Display(d_13_sandwich_, _dafny.SeqWithoutIsStrInference([_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tortila")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "tomato")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lactose")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ham"))]))
        # _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        # default__.Display(d_13_sandwich_, _dafny.SeqWithoutIsStrInference([_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "lactose")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ham"))]))
        # _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        # default__.Display(d_13_sandwich_, _dafny.SeqWithoutIsStrInference([_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ham"))]))
        # _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))
        # default__.Display(d_13_sandwich_, _dafny.SeqWithoutIsStrInference([_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "ham")), _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "chicken"))]))


class NodeType:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [NodeType_Normal(), NodeType_Choice()]
    @classmethod
    def default(cls, ):
        return lambda: NodeType_Normal()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Normal(self) -> bool:
        return isinstance(self, NodeType_Normal)
    @property
    def is_Choice(self) -> bool:
        return isinstance(self, NodeType_Choice)

class NodeType_Normal(NodeType, NamedTuple('Normal', [])):
    def __dafnystr__(self) -> str:
        return f'NodeType.Normal'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, NodeType_Normal)
    def __hash__(self) -> int:
        return super().__hash__()

class NodeType_Choice(NodeType, NamedTuple('Choice', [])):
    def __dafnystr__(self) -> str:
        return f'NodeType.Choice'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, NodeType_Choice)
    def __hash__(self) -> int:
        return super().__hash__()


class FoodTree:
    @classmethod
    def default(cls, ):
        return lambda: FoodTree_FoodNode(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), False, NodeType.default()(), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_FoodNode(self) -> bool:
        return isinstance(self, FoodTree_FoodNode)

class FoodTree_FoodNode(FoodTree, NamedTuple('FoodNode', [('name', Any), ('isIngredient', Any), ('nodeType', Any), ('children', Any)])):
    def __dafnystr__(self) -> str:
        return f'FoodTree.FoodNode({self.name.VerbatimString(True)}, {_dafny.string_of(self.isIngredient)}, {_dafny.string_of(self.nodeType)}, {_dafny.string_of(self.children)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, FoodTree_FoodNode) and self.name == __o.name and self.isIngredient == __o.isIngredient and self.nodeType == __o.nodeType and self.children == __o.children
    def __hash__(self) -> int:
        return super().__hash__()


class FoodLabel:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [FoodLabel_Safe(), FoodLabel_Warning(), FoodLabel_Unsafe()]
    @classmethod
    def default(cls, ):
        return lambda: FoodLabel_Safe()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Safe(self) -> bool:
        return isinstance(self, FoodLabel_Safe)
    @property
    def is_Warning(self) -> bool:
        return isinstance(self, FoodLabel_Warning)
    @property
    def is_Unsafe(self) -> bool:
        return isinstance(self, FoodLabel_Unsafe)

class FoodLabel_Safe(FoodLabel, NamedTuple('Safe', [])):
    def __dafnystr__(self) -> str:
        return f'FoodLabel.Safe'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, FoodLabel_Safe)
    def __hash__(self) -> int:
        return super().__hash__()

class FoodLabel_Warning(FoodLabel, NamedTuple('Warning', [])):
    def __dafnystr__(self) -> str:
        return f'FoodLabel.Warning'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, FoodLabel_Warning)
    def __hash__(self) -> int:
        return super().__hash__()

class FoodLabel_Unsafe(FoodLabel, NamedTuple('Unsafe', [])):
    def __dafnystr__(self) -> str:
        return f'FoodLabel.Unsafe'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, FoodLabel_Unsafe)
    def __hash__(self) -> int:
        return super().__hash__()


class LabeledTree:
    @classmethod
    def default(cls, ):
        return lambda: LabeledTree_LabeledNode(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")), FoodLabel.default()(), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_LabeledNode(self) -> bool:
        return isinstance(self, LabeledTree_LabeledNode)

class LabeledTree_LabeledNode(LabeledTree, NamedTuple('LabeledNode', [('name', Any), ('labelname', Any), ('children', Any)])):
    def __dafnystr__(self) -> str:
        return f'LabeledTree.LabeledNode({self.name.VerbatimString(True)}, {_dafny.string_of(self.labelname)}, {_dafny.string_of(self.children)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, LabeledTree_LabeledNode) and self.name == __o.name and self.labelname == __o.labelname and self.children == __o.children
    def __hash__(self) -> int:
        return super().__hash__()
    

from typing import Any, List, Tuple


class RawNode:
    def __init__(self, name: str, indent: int):
        self.name = name.strip()
        self.indent = indent
        self.children: List['RawNode'] = []

    def __repr__(self):
        return f"{' ' * self.indent}{self.name}"


def parse_tree(lines: List[str]) -> RawNode:
    stack: List[Tuple[int, RawNode]] = []

    for line in lines:
        if line.strip() == "":
            continue
        indent = len(line) - len(line.lstrip())
        node = RawNode(line.strip(), indent)

        while stack and indent <= stack[-1][0]:
            stack.pop()

        if stack:
            stack[-1][1].children.append(node)
        stack.append((indent, node))

    # Return root node (the one with minimal indent)
    while len(stack) > 1:
        stack.pop()
    return stack[0][1] if stack else None


def build_food_tree(node: RawNode, default__) -> Any:
    if "(optional)" in node.name:
        clean_name = node.name.replace(" (optional)", "")
        # Wrap children into a new subnode
        inner = RawNode(clean_name, node.indent + 1)
        inner.children = node.children
        return default__.Optional(build_food_tree(inner, default__))

    clean_name = node.name.replace(" (choose one)", "")
    dafny_name = _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, clean_name))
    children = _dafny.SeqWithoutIsStrInference([build_food_tree(child, default__) for child in node.children])

    if " (choose one)" in node.name:
        return default__.ChooseOne(dafny_name, children)
    elif len(node.children) == 0:
        return default__.Ingredient(dafny_name)
    else:
        return default__.IngredientWithSubingredients(dafny_name, children)


import os

def updated_main_from_file(default__):
    # filepath = "data/food_tree.txt"
    filepath = os.path.join(os.path.dirname(__file__), "data", "food_tree.txt")
    with open(filepath, "r") as f:
        lines = f.readlines()

    raw_root = parse_tree(lines)
    sandwich_tree = build_food_tree(raw_root, default__)
    
    # allergen_sets = [
    #     ["tortila", "tomato", "lactose", "ham"],
    #     ["lactose", "ham"],
    #     ["ham"],
    #     ["ham", "chicken"],
    # ]

    allergen_path = os.path.join(os.path.dirname(__file__), "data", "allergen.txt")

    # Read allergen sets from file
    allergen_sets = []
    with open(allergen_path, "r") as f:
        for line in f:
            line = line.strip()
            if line:
                allergens = [s.strip() for s in line.split(",")]
                allergen_sets.append(allergens)

    for allergens in allergen_sets:
        dafny_allergens = _dafny.SeqWithoutIsStrInference([
            _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, a)) for a in allergens
        ])
        default__.Display(sandwich_tree, dafny_allergens)
        _dafny.print(_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n")).VerbatimString(False))


