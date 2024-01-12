import Regex.Unicode.Unicode

namespace Unicode

/-!
## Unicode

Support for [Unicode Regular Expressions Level 1](https://www.unicode.org/reports/tr18/)
like *\p{x}* where x is a
- [general category](https://www.unicode.org/reports/tr18/#General_Category_Property),
- [full property](https://www.unicode.org/reports/tr18/#Full_Properties),
- [script property](https://www.unicode.org/reports/tr18/#Script_Property).

see:
- `Unicode.rangesOfGeneralCategory`
- `Unicode.rangesOfNamedProperty`

docs:
- [Unicode Character Database](https://www.unicode.org/Public/12.1.0/ucd/)
- [Compatibility_Properties](https://www.unicode.org/reports/tr18/#Compatibility_Properties)
- [Word_Boundaries](https://www.unicode.org/reports/tr29/#Word_Boundaries)

-/
