import Init.Meta
import Regex

open Lean Lean.Syntax

namespace Test.Grammar

def ofExcept (x : Except String $ TSyntax `sequence) : Syntax :=
  match x with
  | .ok x => x
  | .error _ => Syntax.atom .none ""

def syntaxOf'ab' : Syntax :=
  Syntax.node .none `sequence #[
    Syntax.node .none `literal #[Syntax.atom .none "a"],
    Syntax.node .none `literal #[Syntax.atom .none "b"]
  ]

def «syntaxOf'[a-b]'» : Syntax :=
  Syntax.node .none `sequence #[
    Syntax.node .none `characterClass #[
      Syntax.node .none `literal #[Syntax.atom .none "a"],
      Syntax.node .none `hyphen #[Syntax.atom .none "-"],
      Syntax.node .none `literal #[Syntax.atom .none "b"]
    ]
  ]

def «syntaxOf'\\x{20}'» : Syntax :=
  Syntax.node .none `sequence #[
    Syntax.node .none `literal #[Syntax.atom .none " "]
  ]

def «syntaxOf'\\123'» : Syntax :=
  Syntax.node .none `sequence #[
    Syntax.node .none `literal #[Syntax.atom .none "S"]
  ]

def «syntaxOf'a{1,2}'» : Syntax :=
  Syntax.node .none `sequence #[
    Syntax.node .none `literal #[Syntax.atom .none "a"],
    Syntax.node .none `repetition #[
      Syntax.node .none `repetitionLeft #[Syntax.atom .none "1"],
      Syntax.node .none `repetitionRight #[Syntax.atom .none "2"],
      Syntax.node .none `repetitionModifier #[Syntax.atom .none ""]
    ]
  ]

def «translatedSyntaxOf'a{1,2}'» : Syntax :=
  Syntax.node .none `sequence #[
    Syntax.node .none `repetition #[
      Syntax.node .none `repetitionLeft #[Syntax.atom .none "1"],
      Syntax.node .none `repetitionRight #[Syntax.atom .none "2"],
      Syntax.node .none `repetitionModifier #[Syntax.atom .none ""],
      Syntax.node .none `literal #[Syntax.atom .none "a"]
    ]
  ]

def «syntaxOf'a|b'» : Syntax :=
  Syntax.node .none `sequence #[
    Syntax.node .none `literal #[Syntax.atom .none "a"],
    Syntax.node .none `verticalBar #[Syntax.atom .none "|"],
    Syntax.node .none `literal #[Syntax.atom .none "b"]
  ]

def «syntaxOf'(a)'» : Syntax :=
  Syntax.node .none `sequence #[
    Syntax.node .none `group #[
      Syntax.node .none `capturingGroup #[Syntax.atom .none ""],
      Syntax.node .none `literal #[Syntax.atom .none "a"]
    ]
  ]

def «translatedSyntaxOf'(a|b)'» : Syntax :=
  Syntax.node .none `sequence #[
    Syntax.node .none `group #[
      Syntax.node .none `capturingGroup #[Syntax.atom .none ""],
      Syntax.node .none `alternatives #[
        Syntax.node .none `literal #[Syntax.atom .none "a"],
        Syntax.node .none `literal #[Syntax.atom .none "b"]
      ]
    ]
  ]

def «translatedSyntaxOf'a|b|c'» : Syntax :=
  Syntax.node .none `sequence #[
    Syntax.node .none `alternatives #[
       Syntax.node .none `literal #[Syntax.atom .none "a"],
       Syntax.node .none `literal #[Syntax.atom .none "b"],
      Syntax.node .none `literal #[Syntax.atom .none "c"]
    ]
  ]

def «translatedSyntaxOf'[a-bc]'» : Syntax :=
  Syntax.node .none `sequence #[
    Syntax.node .none `characterClass #[
      Syntax.node .none `range #[
        Syntax.node .none `literal #[Syntax.atom .none "a"],
        Syntax.node .none `literal #[Syntax.atom .none "b"]
      ],
      Syntax.node .none `literal #[Syntax.atom .none "c"]
    ]
  ]

example : (Regex.Grammar.parse "ab" default |> ofExcept) == syntaxOf'ab' := by native_decide

example : (Regex.Grammar.parse "[a-b]" default |> ofExcept) == «syntaxOf'[a-b]'» := by native_decide

example : (Regex.Grammar.parse "\\x{20}" default |> ofExcept) == «syntaxOf'\\x{20}'» := by native_decide

example : (Regex.Grammar.parse "\\123" default |> ofExcept) == «syntaxOf'\\123'» := by native_decide

example : (Regex.Grammar.parse "a{1,2}" default |> ofExcept) == «syntaxOf'a{1,2}'» := by native_decide

example : (Regex.Grammar.parse "a|b" default |> ofExcept) == «syntaxOf'a|b'» := by native_decide

example : (Regex.Grammar.parse "(a)" default |> ofExcept) == «syntaxOf'(a)'» := by native_decide

example : ((Regex.Grammar.parse "(a|b)" default >>= Regex.Grammar.translate) |> ofExcept)
            == «translatedSyntaxOf'(a|b)'» := by native_decide

example : ((Regex.Grammar.parse "a|b|c" default >>= Regex.Grammar.translate) |> ofExcept)
            == «translatedSyntaxOf'a|b|c'» := by native_decide

example : ((Regex.Grammar.parse "a{1,2}" default >>= Regex.Grammar.translate) |> ofExcept)
            == «translatedSyntaxOf'a{1,2}'» := by native_decide

example : ((Regex.Grammar.parse "[a-bc]" default >>= Regex.Grammar.translate) |> ofExcept)
            == «translatedSyntaxOf'[a-bc]'» := by native_decide

example : ((Regex.Grammar.parse "ab" default >>= Regex.Grammar.translate) |> ofExcept)
            == (Regex.Grammar.parse "ab" default |> ofExcept) := by native_decide

example : ((Regex.Grammar.parse "(ab)" default >>= Regex.Grammar.translate) |> ofExcept)
            == (Regex.Grammar.parse "(ab)" default  |> ofExcept) := by native_decide
