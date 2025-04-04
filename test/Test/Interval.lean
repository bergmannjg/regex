import Regex

namespace Test.NonemptyInterval

example : (⟨⟨'b', 'c'⟩, by simp +arith⟩ : NonemptyInterval Char)
  = Interval.intersection ⟨⟨'a', 'c'⟩, by simp +arith⟩ ⟨⟨'b', 'e'⟩, by simp +arith⟩ := by rfl

namespace Test.NonemptyInterval.Intersection

def iv1 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'c'⟩, by simp +arith⟩, ⟨⟨'g', 'k'⟩, by simp +arith⟩]
def iv2 : Array $ NonemptyInterval Char :=
            #[⟨⟨'b', 'e'⟩, by simp +arith⟩, ⟨⟨'j', 'l'⟩, by simp +arith⟩, ⟨⟨'m', 'n'⟩, by simp +arith⟩]
def iv : Array $ NonemptyInterval Char := #[⟨⟨'b', 'c'⟩, by simp +arith⟩, ⟨⟨'j', 'k'⟩, by simp +arith⟩]

example : iv =
    (IntervalSet.intersection
        (IntervalSet.canonicalize iv1)
        (IntervalSet.canonicalize iv2)).intervals := by
  native_decide

end Test.NonemptyInterval.Intersection

namespace Test.NonemptyInterval.Difference

def iv1 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'e'⟩, by simp +arith⟩]
def iv2 : Array $ NonemptyInterval Char := #[⟨⟨'b', 'c'⟩, by simp +arith⟩]
def iv : Array $ NonemptyInterval Char := #[⟨⟨'a', 'a'⟩, by simp +arith⟩, ⟨⟨'d', 'e'⟩, by simp +arith⟩]

example : iv =
    (IntervalSet.difference (IntervalSet.canonicalize iv1) (IntervalSet.canonicalize iv2)).intervals := by
  native_decide

end Test.NonemptyInterval.Difference

namespace Test.NonemptyInterval.SymmetricDifference

def iv1 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'c'⟩, by simp +arith⟩]
def iv2 : Array $ NonemptyInterval Char := #[⟨⟨'b', 'd'⟩, by simp +arith⟩]
def iv : Array $ NonemptyInterval Char := #[⟨⟨'a', 'a'⟩, by simp +arith⟩, ⟨⟨'d', 'd'⟩, by simp +arith⟩]

example : iv =
    (IntervalSet.symmetric_difference (IntervalSet.canonicalize iv1) (IntervalSet.canonicalize iv2)).intervals
  := by native_decide

end Test.NonemptyInterval.SymmetricDifference

namespace Test.NonemptyInterval.Canonicalize

def ivnc : Array $ NonemptyInterval Char := #[⟨⟨'a', 'c'⟩, by simp +arith⟩, ⟨⟨'b', 'd'⟩, by simp +arith⟩]
def iv : Array $ NonemptyInterval Char := #[⟨⟨'a', 'd'⟩, by simp +arith⟩]

example : iv = (IntervalSet.canonicalize ivnc).intervals := by native_decide

def ivnc2 : Array $ NonemptyInterval Char := #[
      ⟨⟨'b', 'b'⟩, by simp +arith⟩,
      ⟨⟨'C', 'C'⟩, by simp +arith⟩,
      ⟨⟨'B', 'B'⟩, by simp +arith⟩,
      ⟨⟨'c', 'c'⟩, by simp +arith⟩]
def iv2 : Array $ NonemptyInterval Char := #[
      ⟨⟨'B', 'C'⟩, by simp +arith⟩,
      ⟨⟨'b', 'c'⟩, by simp +arith⟩]

example : iv2 = (IntervalSet.canonicalize ivnc2).intervals := by native_decide

def ivnc3 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'c'⟩, by simp +arith⟩, ⟨⟨'d', 'd'⟩, by simp +arith⟩]
def iv3 : Array $ NonemptyInterval Char := #[⟨⟨'a', 'd'⟩, by simp +arith⟩]

example : iv3 = (IntervalSet.canonicalize ivnc3).intervals := by native_decide

def ivnc4 : Array $ NonemptyInterval Char := #[
  /- 2275 2281 -/ ⟨⟨'ࣣ', 'ࣩ'⟩, by simp +arith⟩,
  /- 2275 2307 -/ ⟨⟨'ࣣ', 'ः'⟩, by simp +arith⟩,
  /- 2288 2306 -/ ⟨⟨'ࣰ', 'ं'⟩, by simp +arith⟩,
  /- 2307 2307 -/ ⟨⟨'ः', 'ः'⟩, by simp +arith⟩,
  /- 2308 2361 -/ ⟨⟨'ऄ', 'ह'⟩, by simp +arith⟩,
  /- 2362 2362 -/ ⟨⟨'ऺ', 'ऺ'⟩, by simp +arith⟩,
  /- 2362 2364 -/ ⟨⟨'ऺ', '़'⟩, by simp +arith⟩,
  /- 2363 2363 -/ ⟨⟨'ऻ', 'ऻ'⟩, by simp +arith⟩]

def iv4 : Array $ NonemptyInterval Char :=  #[⟨⟨'ࣣ', '़'⟩, by simp +arith⟩]

example : iv4 = (IntervalSet.canonicalize ivnc4).intervals := by native_decide

end Test.NonemptyInterval.Canonicalize

namespace Test.NonemptyInterval.Unique

def iv : Array $ NonemptyInterval Char := #[
      ⟨⟨'C', 'C'⟩, by simp +arith⟩,
      ⟨⟨'b', 'b'⟩, by simp +arith⟩,
      ⟨⟨'c', 'c'⟩, by simp +arith⟩]

def iv1 : Array $ NonemptyInterval Char := #[
      ⟨⟨'C', 'C'⟩, by simp +arith⟩,
      ⟨⟨'b', 'b'⟩, by simp +arith⟩,
      ⟨⟨'b', 'b'⟩, by simp +arith⟩,
      ⟨⟨'c', 'c'⟩, by simp +arith⟩]

example : iv = Intervals.unique iv1 := by native_decide

def iv2 : Array $ NonemptyInterval Char := #[
      ⟨⟨'C', 'C'⟩, by simp +arith⟩,
      ⟨⟨'C', 'C'⟩, by simp +arith⟩,
      ⟨⟨'b', 'b'⟩, by simp +arith⟩,
      ⟨⟨'c', 'c'⟩, by simp +arith⟩]

example : iv = Intervals.unique iv2 := by native_decide

def iv3 : Array $ NonemptyInterval Char := #[
      ⟨⟨'C', 'C'⟩, by simp +arith⟩,
      ⟨⟨'C', 'C'⟩, by simp +arith⟩,
      ⟨⟨'b', 'b'⟩, by simp +arith⟩,
      ⟨⟨'b', 'b'⟩, by simp +arith⟩,
      ⟨⟨'c', 'c'⟩, by simp +arith⟩,
      ⟨⟨'c', 'c'⟩, by simp +arith⟩]

example : iv = Intervals.unique iv3 := by native_decide

end Test.NonemptyInterval.Unique

end Test.NonemptyInterval
