BeginPackage["ExpressionManipulation`"]

ReplaceAllList::usage="";
ReverseFold::usage="";
UnsortedComplement::usage="";
MutualComplement::usage="";
MutualUnsortedComplement::usage="";
PositionRules::usage="";
NamedPart::usage="";
SortByNamedPart::usage="";
HashSet::usage="";
HashSetDelayed::usage="";
SelectFree::usage="";
NullFree::usage="";
Slice::usage="";
SplitAt::usage="";
MultipleDrop::usage="";
OrderBy::usage="";
Duplicates::usage="";
RelativeFrequencies::usage="";

Begin["Private`"];

(* General expression manipulation functions *)

(* This comes from the ReplaceList documentation *)

ReplaceAllList[expr_,rules_] :=
    Block[ {i},
        Join[ReplaceList[expr,rules],If[ AtomQ[expr],
            {}, Join@@Table[ReplacePart[expr,#,i]&/@ReplaceAllList[expr[[i]],rules],{i,Length[expr]}]
        ]]
    ];

(* ReverseFold: Fold over lists from end to beginning *)

ReverseFold[f_,x_,{a_}] :=
    f[x,a];

ReverseFold[f_,x_,{a_,b__}] :=
    f[x,ReverseFold[f,a,{b}]];

(* Complement operations *)

UnsortedComplement[x_List, y__List] :=
	Replace[x, Dispatch[(#1 :> Sequence[] & ) /@ Union[y]], 1]

MutualComplement[l1_, l2_]:=
	{Complement[l1,l2], Complement[l2,l1]}

MutualUnsortedComplement[l1_, l2_]:=
	{UnsortedComplement[l1,l2], UnsortedComplement[l2,l1]}

(* Named parts *)

PositionRules[list_]:=
	MapIndexed[Rule[#1, First@#2]&, list]

NamedPart[list_, names_, part__] :=
 Part[list, Apply[Sequence, {part} /. PositionRules@names]]

SortByNamedPart[expr_, names_, part_] :=
 SortBy[expr, NamedPart[#, names, part] &]

(* Automate Set assignments over lists of expressions *)

HashSet[symbol_, expr_] :=
 Block[{}, ClearAll[symbol]; symbol[_] = Null;
  Set[symbol@#1, #2] & @@@ expr]

HashSetDelayed[symbol_, expr_] :=
 Block[{}, ClearAll[symbol]; symbol[_] = Null;
  SetDelayed[symbol@#1, #2] & @@@ expr]

(* Remove nulls *)

SelectFree[list_,patt_]:=
	Select[list, FreeQ[#, HoldPattern@patt]&]

NullFree[list_]:=
	SelectFree[list, Null]

(* Miscellaneous *)

Slice[{min_,max_},n_] :=
    Range[min,max,(max-min)/(n-1)];

SplitAt[exp_,pos_] :=
    {Take[exp,{1,pos-1}],Take[exp,{pos+1,-1}]};

MultipleDrop[list_,pos_] :=
    Fold[Drop[#1,{#2}]&,list,(#-Range[0,Length[#]-1])&@Union@pos];

(* This has a bug when the list to be ordered has duplicate elements *)

OrderBy::rule = "List `1` is not a list of integers";

OrderBy[list_, ordering_] :=
	Block[{posrules = Append[MapIndexed[#1 -> First@#2 &, Select[ordering,MemberQ[list, #]&]],_->Infinity], order},
	SortBy[list, (#/.posrules)&]
		]

Duplicates[list_, foo_] :=
     Select[Union/@GatherBy[list,
     foo], Length@# > 1 &]

RelativeFrequencies[set_] :=
    With[ {l = Length[set]},
        ({#1[[1]],(#1[[2]])/l}&)/@Tally[set]
    ];

End[];
EndPackage[];