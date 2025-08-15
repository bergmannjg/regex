import UnicodeBasic
import Regex.Unicode.Utils

/-!
## Unicode character properties

A unicode character may have properties. A property has a name
and a type (`Unicode.PropertyType`) and may have values.

see
- [Basic Unicode Support Level 1 properties](https://unicode.org/reports/tr18/#RL1.2)
- [Extended Unicode Support Level 2 full properties](https://www.unicode.org/reports/tr18/#Full_Properties)
-/
namespace Unicode

/-- The type of a property -/
inductive PropertyType where
  | Catalog : PropertyType
  | Enumeration : PropertyType
  | Binary : PropertyType
  | String : PropertyType
  | Numeric : PropertyType
  | Miscellaneous : PropertyType

/-- Property names,
    extends [Basic Unicode Support Level 1 properties](https://unicode.org/reports/tr18/#RL1.2) -/
inductive PropertyName where
  | General_Category : PropertyName
  | Script : PropertyName
  | Alphabetic : PropertyName
  | Uppercase : PropertyName
  | Lowercase : PropertyName
  | White_Space : PropertyName
  | Noncharacter_Code_Point : PropertyName
  | Default_Ignorable_Code_Point : PropertyName
  | ANY : PropertyName
  | ASCII : PropertyName
  | ASSIGNED : PropertyName
  | Numeric_Value : PropertyName
  | Hex_Digit : PropertyName
  | ASCII_Hex_Digit : PropertyName
  | Emoji : PropertyName
  | Extended_Pictographic : PropertyName
  | Grapheme_Cluster_Break : PropertyName
  | Sentence_Break : PropertyName
  | Word_Break : PropertyName
  | Math : PropertyName
  | Regional_Indicator : PropertyName
deriving BEq

instance : ToString PropertyName where
  toString s := match s with
    | .General_Category => "General_Category"
    | .Script => "Script"
    | .Alphabetic => "Alphabetic"
    | .Uppercase => "Uppercase"
    | .Lowercase => "Lowercase"
    | .White_Space => "White_Space"
    | .Noncharacter_Code_Point => "Noncharacter_Code_Point"
    | .Default_Ignorable_Code_Point => "Default_Ignorable_Code_Point"
    | .ANY => "ANY"
    | .ASCII => "ASCII"
    | .ASSIGNED => "ASSIGNED"
    | .Numeric_Value => "Numeric_Value"
    | .Hex_Digit => "Hex_Digit"
    | .ASCII_Hex_Digit => "ASCII_Hex_Digit"
    | .Emoji => "Emoji"
    | .Extended_Pictographic => "Extended_Pictographic"
    | .Grapheme_Cluster_Break => "Grapheme_Cluster_Break"
    | .Sentence_Break => "Sentence_Break"
    | .Word_Break => "Word_Break"
    | .Math => "Math"
    | .Regional_Indicator => "Regional_Indicator"

/-- get type of property -/
def typeOfProperty : PropertyName -> PropertyType
  | .General_Category => .Enumeration
  | .Script => .Enumeration
  | .Alphabetic => .Binary
  | .Uppercase => .Binary
  | .Lowercase => .Binary
  | .White_Space => .Binary
  | .Noncharacter_Code_Point =>.Binary
  | .Default_Ignorable_Code_Point => .Binary
  | .ANY => .Binary
  | .ASCII => .Binary
  | .ASSIGNED => .Binary
  | .Numeric_Value => .Numeric
  | .Hex_Digit => .Binary
  | .ASCII_Hex_Digit => .Binary
  | .Emoji => .Binary
  | .Extended_Pictographic => .Binary
  | .Grapheme_Cluster_Break => .Enumeration
  | .Sentence_Break => .Enumeration
  | .Word_Break => .Enumeration
  | .Math => .Binary
  | .Regional_Indicator => .Binary

/-- Property name palias -/
structure PropertyAlias where
  short : String
  long : String
  propertyName : PropertyName

/-- part of [PropertyAliases](https://www.unicode.org/Public/12.1.0/ucd/PropertyAliases.txt),
    todo: read from file -/
private def propertyAliases : Array PropertyAlias := #[
  ⟨"gc", "General_Category", .General_Category⟩,
  ⟨"sc", "Script", .Script⟩,
  ⟨"wspace", "White_Space", .White_Space⟩,
  ⟨"space", "White_Space", .White_Space⟩,
  ⟨"alpha", "Alphabetic", .Alphabetic⟩,
  ⟨"nv", "Numeric_Value", .Numeric_Value⟩,
  ⟨"upper", "Uppercase", .Uppercase⟩,
  ⟨"lower", "Lowercase", .Lowercase⟩,
  ⟨"emoji", "Emoji", .Emoji⟩,
  ⟨"extendedpictographic", "Extended_Pictographic", .Extended_Pictographic⟩,
  ⟨"gcb", "Grapheme_Cluster_Break", .Grapheme_Cluster_Break⟩,
  ⟨"sb", "Sentence_Break", .Sentence_Break⟩,
  ⟨"wb", "Word_Break", .Word_Break⟩,
  ⟨"math", "Math", .Math⟩,
  ⟨"ri", "Regional_Indicator", .Regional_Indicator⟩
]

def matchPropertyAlias (s : String) (palias : PropertyAlias) : Bool :=
  let sn := normalize s
  let ln := normalize palias.long
  sn = palias.short || sn = ln

/-- part of [PropertyValueAliases](https://www.unicode.org/Public/12.1.0/ucd/PropertyValueAliases.txt),
    todo: read from file -/
private def propertyValueAliases : Array PropertyAlias := #[
  ⟨"ri", "Regional_Indicator", .Grapheme_Cluster_Break⟩
]

private def matchPropertyValueAlias (name : PropertyName) (s : String) (palias : PropertyAlias)
    : Bool :=
  let sn := normalize s
  let ln := normalize palias.long
  if palias.propertyName != name then false
  else sn = palias.short || sn = ln

/-- get PropertyValueAlias of property name and value -/
def getPropertyValueAlias (name : PropertyName) (val : String) : Option PropertyAlias :=
  match propertyValueAliases.find? (matchPropertyValueAlias name val) with
  | some palias => palias
  | none => none

/-- get PropertyName of property name `s` -/
def ofName? (s : String) : Option PropertyName :=
  match propertyAliases.find? (matchPropertyAlias s) with
  | some palias => palias.propertyName
  | none => none

/-- get GeneralCategory of long property value `s` -/
def GeneralCategory.ofLong? (s : Substring) : Option GC :=
  match s with
  | "Uppercase_Letter" => some GC.Lu
  | "Lowercase_Letter" => some GC.Ll
  | "Titlecase_Letter" => some GC.Lt
  | "Cased_Letter" => some GC.LC
  | "Modifier_Letter" => some GC.Lm
  | "Other_Letter" => some GC.Lo
  | "Letter" => some GC.L
  | "Nonspacing_Mark" => some GC.Mn
  | "Spacing_Mark" => some GC.Mc
  | "Enclosing_Mark" => some GC.Me
  | "Mark" => some GC.M
  | "Decimal_Number" => some GC.Nd
  | "Letter_Number" => some GC.Nl
  | "Other_Number" => some GC.No
  | "Number" => some GC.N
  | "Connector_Punctuation" => some GC.Pc
  | "Dash_Punctuation" => some GC.Pd
  | "Open_Punctuation" => some GC.Ps
  | "Close_Punctuation" => some GC.Pe
  | "Initial_Punctuation" => some GC.Pi
  | "Final_Punctuation" => some GC.Pf
  | "Other_Punctuation" => some GC.Po
  | "Punctuation" => some GC.P
  | "Math_Symbol" => some GC.Sm
  | "Currency_Symbol" => some GC.Sc
  | "Modifier_Symbol" => some GC.Sk
  | "Other_Symbol" => some GC.So
  | "Symbol" => some GC.S
  | "Space_Separator" => some GC.Zs
  | "Line_Separator" => some GC.Zl
  | "Paragraph_Separator" => some GC.Zp
  | "Separator" => some GC.Z
  | "Control" => some GC.Cc
  | "Format" => some GC.Cf
  | "Surrogate" => some GC.Cs
  | "Private_Use" => some GC.Co
  | "Unassigned" => some GC.Cn
  | "Other" => some GC.C
  | _ => none

/-- get GeneralCategory of property value `s` -/
def GeneralCategory.ofValue? (s : Substring) : Option GC :=
  GC.ofAbbrev? s <|> GeneralCategory.ofLong? s

/-- get PropertyName of property  value -/
def ofValue? (s : String) : Option PropertyName :=
  match GeneralCategory.ofValue? s with
  | some _ => some .General_Category
  | none => none

/-- get PropertyName of compatibility property name,
    see [Compatibility_Properties](https://www.unicode.org/reports/tr18/#Compatibility_Properties) -/
def ofCompatibilityPropertyName? (s : String)
    : Option $ Array (PropertyName × Option String) :=
  /- alpha, lower, upper, space via palias -/
  match normalize s with
  | "punct" => some #[(PropertyName.General_Category, GC.P.toAbbrev!)]
  | "digit" => some #[(PropertyName.General_Category, GC.Nd.toAbbrev!)]
  | "xdigit" => some #[(PropertyName.Hex_Digit, none)]
  | "cntrl" => some #[(PropertyName.General_Category, GC.Cc.toAbbrev!)]
  | "word" => -- \p{alpha} \p{gc=Mark} \p{digit} \p{gc=Connector_Punctuation} \p{Join_Control}
      some #[
        (PropertyName.Alphabetic, none),
        (PropertyName.General_Category, GC.M.toAbbrev!),
        (PropertyName.General_Category, GC.Nd.toAbbrev!),
        (PropertyName.General_Category, GC.Pc.toAbbrev!)
      ]
  | _ => none
