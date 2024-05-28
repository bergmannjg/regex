import Regex

namespace Test.NonemptyInterval

example : (⟨⟨'b', 'c'⟩, by simp_arith⟩ : NonemptyInterval Char)
  = Interval.intersection ⟨⟨'a', 'c'⟩, by simp_arith⟩ ⟨⟨'b', 'e'⟩, by simp_arith⟩ := by rfl

namespace Test.NonemptyInterval.Intersection

def iv1 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'c'⟩, by simp_arith⟩, ⟨⟨'g', 'k'⟩, by simp_arith⟩]
def iv2 : Array $ NonemptyInterval Char :=
            #[⟨⟨'b', 'e'⟩, by simp_arith⟩, ⟨⟨'j', 'l'⟩, by simp_arith⟩, ⟨⟨'m', 'n'⟩, by simp_arith⟩]
def iv : Array $ NonemptyInterval Char := #[⟨⟨'b', 'c'⟩, by simp_arith⟩, ⟨⟨'j', 'k'⟩, by simp_arith⟩]

example : iv =
    (IntervalSet.intersection
        (IntervalSet.canonicalize iv1)
        (IntervalSet.canonicalize iv2)).intervals := by
  native_decide

end Test.NonemptyInterval.Intersection

namespace Test.NonemptyInterval.Difference

def iv1 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'e'⟩, by simp_arith⟩]
def iv2 : Array $ NonemptyInterval Char := #[⟨⟨'b', 'c'⟩, by simp_arith⟩]
def iv : Array $ NonemptyInterval Char := #[⟨⟨'a', 'a'⟩, by simp_arith⟩, ⟨⟨'d', 'e'⟩, by simp_arith⟩]

example : iv =
    (IntervalSet.difference (IntervalSet.canonicalize iv1) (IntervalSet.canonicalize iv2)).intervals := by
  native_decide

end Test.NonemptyInterval.Difference

namespace Test.NonemptyInterval.SymmetricDifference

def iv1 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'c'⟩, by simp_arith⟩]
def iv2 : Array $ NonemptyInterval Char := #[⟨⟨'b', 'd'⟩, by simp_arith⟩]
def iv : Array $ NonemptyInterval Char := #[⟨⟨'a', 'a'⟩, by simp_arith⟩, ⟨⟨'d', 'd'⟩, by simp_arith⟩]

example : iv =
    (IntervalSet.symmetric_difference (IntervalSet.canonicalize iv1) (IntervalSet.canonicalize iv2)).intervals
  := by native_decide

end Test.NonemptyInterval.SymmetricDifference

namespace Test.NonemptyInterval.Canonicalize

def ivnc : Array $ NonemptyInterval Char := #[⟨⟨'a', 'c'⟩, by simp_arith⟩, ⟨⟨'b', 'd'⟩, by simp_arith⟩]
def iv : Array $ NonemptyInterval Char := #[⟨⟨'a', 'd'⟩, by simp_arith⟩]

example : iv = (IntervalSet.canonicalize ivnc).intervals := by native_decide

def ivnc2 : Array $ NonemptyInterval Char := #[
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'B', 'B'⟩, by simp_arith⟩,
      ⟨⟨'c', 'c'⟩, by simp_arith⟩]
def iv2 : Array $ NonemptyInterval Char := #[
      ⟨⟨'B', 'C'⟩, by simp_arith⟩,
      ⟨⟨'b', 'c'⟩, by simp_arith⟩]

example : iv2 = (IntervalSet.canonicalize ivnc2).intervals := by native_decide

def ivnc3 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'c'⟩, by simp_arith⟩, ⟨⟨'d', 'd'⟩, by simp_arith⟩]
def iv3 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'd'⟩, by simp_arith⟩]

example : iv3 = (IntervalSet.canonicalize ivnc3).intervals := by native_decide

def ivnc4 : Array $ NonemptyInterval Char := #[
  /- 2275 2281 -/ ⟨⟨'ࣣ', 'ࣩ'⟩, by simp_arith⟩,
  /- 2275 2307 -/ ⟨⟨'ࣣ', 'ः'⟩, by simp_arith⟩,
  /- 2288 2306 -/ ⟨⟨'ࣰ', 'ं'⟩, by simp_arith⟩,
  /- 2307 2307 -/ ⟨⟨'ः', 'ः'⟩, by simp_arith⟩,
  /- 2308 2361 -/ ⟨⟨'ऄ', 'ह'⟩, by simp_arith⟩,
  /- 2362 2362 -/ ⟨⟨'ऺ', 'ऺ'⟩, by simp_arith⟩,
  /- 2362 2364 -/ ⟨⟨'ऺ', '़'⟩, by simp_arith⟩,
  /- 2363 2363 -/ ⟨⟨'ऻ', 'ऻ'⟩, by simp_arith⟩]

def iv4 : Array $ NonemptyInterval Char :=  #[⟨⟨'ࣣ', '़'⟩, by simp_arith⟩]

example : iv4 = (IntervalSet.canonicalize ivnc4).intervals := by native_decide

end Test.NonemptyInterval.Canonicalize

namespace Test.NonemptyInterval.Unique

def iv : Array $ NonemptyInterval Char := #[
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'c', 'c'⟩, by simp_arith⟩]

def iv1 : Array $ NonemptyInterval Char := #[
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'c', 'c'⟩, by simp_arith⟩]

example : iv = Intervals.unique iv1 := by native_decide

def iv2 : Array $ NonemptyInterval Char := #[
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'c', 'c'⟩, by simp_arith⟩]

example : iv = Intervals.unique iv2 := by native_decide

def iv3 : Array $ NonemptyInterval Char := #[
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'C', 'C'⟩, by simp_arith⟩,
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'b', 'b'⟩, by simp_arith⟩,
      ⟨⟨'c', 'c'⟩, by simp_arith⟩,
      ⟨⟨'c', 'c'⟩, by simp_arith⟩]

example : iv = Intervals.unique iv3 := by native_decide

end Test.NonemptyInterval.Unique

end Test.NonemptyInterval
