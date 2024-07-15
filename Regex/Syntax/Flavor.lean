namespace Syntax

/-- Flavor of regular expressions -/
inductive Flavor where
  /-- Perl-compatible regular expressions (https://www.pcre.org/current/doc/html/pcre2pattern.html). -/
  | Pcre : Flavor
  /-- Rust-compatible regular expressions (https://docs.rs/regex/latest/regex/#syntax). -/
  | Rust : Flavor
deriving BEq

instance : Inhabited Flavor := ⟨Syntax.Flavor.Pcre⟩

instance : ToString Flavor where
  toString f := match f with | .Pcre => "Pcre" | .Rust => "Rust"

end Syntax
