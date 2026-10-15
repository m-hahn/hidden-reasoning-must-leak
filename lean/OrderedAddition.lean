import Mathlib

/-!
Formalization of the local-divisor construction used in the
Schützenberger/McNaughton--Papert theorem.  This file is intentionally
independent of the Transformer compiler.
-/

namespace OrderedAddition

def IsAperiodic (M : Type*) [Monoid M] : Prop :=
  ∀ x : M, ∃ exponent : ℕ, x ^ exponent = x ^ (exponent + 1)

structure LocalDivisor (M : Type*) [Monoid M] (c : M) where
  value : M
  fromLeft : ∃ right, c * right = value
  fromRight : ∃ left, left * c = value

namespace LocalDivisor

variable {M : Type*} [Monoid M] {c : M}

@[ext] theorem ext {x y : LocalDivisor M c} (h : x.value = y.value) : x = y := by
  cases x
  cases y
  simp_all

noncomputable def leftFactor (x : LocalDivisor M c) : M :=
  Classical.choose x.fromRight

theorem leftFactor_spec (x : LocalDivisor M c) : x.leftFactor * c = x.value :=
  Classical.choose_spec x.fromRight

noncomputable def rightFactor (x : LocalDivisor M c) : M :=
  Classical.choose x.fromLeft

theorem rightFactor_spec (x : LocalDivisor M c) : c * x.rightFactor = x.value :=
  Classical.choose_spec x.fromLeft

noncomputable def mul (x y : LocalDivisor M c) : LocalDivisor M c where
  value := x.leftFactor * c * y.rightFactor
  fromLeft := ⟨x.rightFactor * y.rightFactor, by
    calc
      c * (x.rightFactor * y.rightFactor) =
          (c * x.rightFactor) * y.rightFactor := by simp [mul_assoc]
      _ = x.value * y.rightFactor := by rw [x.rightFactor_spec]
      _ = (x.leftFactor * c) * y.rightFactor := by rw [x.leftFactor_spec]
      _ = x.leftFactor * c * y.rightFactor := rfl⟩
  fromRight := ⟨x.leftFactor * y.leftFactor, by
    calc
      (x.leftFactor * y.leftFactor) * c =
          x.leftFactor * (y.leftFactor * c) := by simp [mul_assoc]
      _ = x.leftFactor * y.value := by rw [y.leftFactor_spec]
      _ = x.leftFactor * (c * y.rightFactor) := by rw [y.rightFactor_spec]
      _ = x.leftFactor * c * y.rightFactor := by simp [mul_assoc]⟩

theorem mul_value_of_factors (x y : LocalDivisor M c) {left right : M}
    (hleft : left * c = x.value) (hright : c * right = y.value) :
    (mul x y).value = left * c * right := by
  simp only [mul]
  calc
    x.leftFactor * c * y.rightFactor = x.value * y.rightFactor := by
      rw [x.leftFactor_spec]
    _ = (left * c) * y.rightFactor := by rw [hleft]
    _ = left * (c * y.rightFactor) := by simp [mul_assoc]
    _ = left * y.value := by rw [y.rightFactor_spec]
    _ = left * (c * right) := by rw [hright]
    _ = left * c * right := by simp [mul_assoc]

def one : LocalDivisor M c := ⟨c, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

noncomputable instance : Monoid (LocalDivisor M c) where
  one := one
  mul := mul
  one_mul x := by
    apply ext
    obtain ⟨right, hright⟩ := x.fromLeft
    change (mul (one (M := M) (c := c)) x).value = x.value
    rw [mul_value_of_factors (one (M := M) (c := c)) x (left := 1)
      (right := right) (by simp [one]) hright]
    simpa using hright
  mul_one x := by
    apply ext
    obtain ⟨left, hleft⟩ := x.fromRight
    change (mul x (one (M := M) (c := c))).value = x.value
    rw [mul_value_of_factors x (one (M := M) (c := c)) (left := left)
      (right := 1) hleft (by simp [one])]
    simpa using hleft
  mul_assoc x y z := by
    apply ext
    obtain ⟨xleft, hxleft⟩ := x.fromRight
    obtain ⟨yleft, hyleft⟩ := y.fromRight
    obtain ⟨yright, hyright⟩ := y.fromLeft
    obtain ⟨zright, hzright⟩ := z.fromLeft
    have hxyLeft : (xleft * yleft) * c = (mul x y).value := by
      rw [mul_value_of_factors x y (left := xleft) (right := yright) hxleft hyright]
      calc
        (xleft * yleft) * c = xleft * (yleft * c) := by simp [mul_assoc]
        _ = xleft * y.value := by rw [hyleft]
        _ = xleft * (c * yright) := by rw [hyright]
        _ = xleft * c * yright := by simp [mul_assoc]
    have hyzRight : c * (yright * zright) = (mul y z).value := by
      rw [mul_value_of_factors y z (left := yleft) (right := zright) hyleft hzright]
      calc
        c * (yright * zright) = (c * yright) * zright := by simp [mul_assoc]
        _ = y.value * zright := by rw [hyright]
        _ = (yleft * c) * zright := by rw [hyleft]
    change (mul (mul x y) z).value = (mul x (mul y z)).value
    rw [mul_value_of_factors (mul x y) z
      (left := xleft * yleft) (right := zright) hxyLeft hzright]
    rw [mul_value_of_factors x (mul y z)
      (left := xleft) (right := yright * zright) hxleft hyzRight]
    calc
      xleft * yleft * c * zright = xleft * (yleft * c) * zright := by
        simp [mul_assoc]
      _ = xleft * y.value * zright := by rw [hyleft]
      _ = xleft * (c * yright) * zright := by rw [hyright]
      _ = xleft * c * (yright * zright) := by simp [mul_assoc]

@[simp] theorem one_value : (1 : LocalDivisor M c).value = c := rfl

noncomputable instance [Fintype M] : Fintype (LocalDivisor M c) :=
  Fintype.ofInjective LocalDivisor.value (fun _ _ h => ext h)

theorem mul_value_of_right_factor (x y : LocalDivisor M c) {right : M}
    (hright : c * right = y.value) :
    (x * y).value = x.value * right := by
  change (mul x y).value = x.value * right
  rw [mul_value_of_factors x y (left := x.leftFactor) (right := right)
    x.leftFactor_spec hright, x.leftFactor_spec]

theorem pow_succ_value (z : LocalDivisor M c) {right : M}
    (hright : c * right = z.value) :
    ∀ exponent : ℕ, (z ^ (exponent + 1)).value = c * right ^ (exponent + 1) := by
  intro exponent
  induction exponent with
  | zero => simpa using hright.symm
  | succ exponent ih =>
      rw [show exponent + 1 + 1 = (exponent + 1) + 1 by omega, pow_succ,
        mul_value_of_right_factor (z ^ (exponent + 1)) z hright, ih, pow_succ]
      simp [pow_succ, mul_assoc]

/-- Local divisors of aperiodic monoids are aperiodic. -/
theorem isAperiodic (hM : IsAperiodic M) :
    IsAperiodic (LocalDivisor M c) := by
  intro z
  obtain ⟨right, hright⟩ := z.fromLeft
  obtain ⟨exponent, hexponent⟩ := hM right
  refine ⟨exponent + 1, ext ?_⟩
  rw [pow_succ_value z hright, pow_succ_value z hright]
  congr 1
  simpa [pow_succ] using congrArg (fun value => value * right) hexponent

private theorem right_inverse_isUnit [Fintype M] {x inverse : M}
    (h : x * inverse = 1) : IsUnit x := by
  let rightMultiply : M → M := fun value => value * inverse
  have hsurjective : Function.Surjective rightMultiply := by
    intro value
    refine ⟨value * x, ?_⟩
    dsimp [rightMultiply]
    simp [mul_assoc, h]
  have hinjective : Function.Injective rightMultiply :=
    Finite.injective_iff_surjective.mpr hsurjective
  have hinverse : inverse * x = 1 := by
    apply hinjective
    dsimp [rightMultiply]
    simp [mul_assoc, h]
  exact ⟨⟨x, inverse, h, hinverse⟩, rfl⟩

theorem isUnit_eq_one (hM : IsAperiodic M) {x : M} (hx : IsUnit x) : x = 1 := by
  obtain ⟨exponent, hexponent⟩ := hM x
  have hpower : IsUnit (x ^ exponent) := hx.pow exponent
  apply hpower.mul_left_cancel
  simpa [pow_succ] using hexponent.symm

/-- For a nonidentity element of a finite aperiodic monoid, its local divisor
is strictly smaller.  This is the terminating measure in the local-divisor
proof of the star-free theorem. -/
theorem card_lt [Fintype M] (hM : IsAperiodic M) (hc : c ≠ 1) :
    Fintype.card (LocalDivisor M c) < Fintype.card M := by
  apply Fintype.card_lt_of_injective_of_not_mem LocalDivisor.value
    (fun _ _ h => ext h) (b := 1)
  intro hone
  obtain ⟨z, hz⟩ := hone
  obtain ⟨right, hright⟩ := z.fromLeft
  have hcunit : IsUnit c := right_inverse_isUnit (by simpa [hz] using hright)
  exact hc (isUnit_eq_one hM hcunit)

end LocalDivisor

/-! ## Star-free languages over a finite alphabet -/

/-- Star-free regular expressions.  A letter node may name any subset of the
fixed alphabet; this is equivalent to a finite union of singleton letters and
is convenient when the alphabet is represented by bit strings. -/
inductive Expression (Alphabet : Type*)
  | empty
  | epsilon
  | letter (predicate : Alphabet → Bool)
  | union (left right : Expression Alphabet)
  | inter (left right : Expression Alphabet)
  | compl (body : Expression Alphabet)
  | concat (left right : Expression Alphabet)

namespace Expression

def Accepts : Expression Alphabet → List Alphabet → Prop
  | .empty, _ => False
  | .epsilon, word => word = []
  | .letter predicate, word => ∃ symbol, word = [symbol] ∧ predicate symbol = true
  | .union left right, word => left.Accepts word ∨ right.Accepts word
  | .inter left right, word => left.Accepts word ∧ right.Accepts word
  | .compl body, word => ¬ body.Accepts word
  | .concat left right, word =>
      ∃ initial final, word = initial ++ final ∧
        left.Accepts initial ∧ right.Accepts final

def all : Expression Alphabet := .compl .empty

def contains (predicate : Alphabet → Bool) : Expression Alphabet :=
  .concat all (.concat (.letter predicate) all)

/-- All words whose letters satisfy `predicate`. -/
def over (predicate : Alphabet → Bool) : Expression Alphabet :=
  .compl (contains fun symbol => !predicate symbol)

def unions : List (Expression Alphabet) → Expression Alphabet
  | [] => .empty
  | expression :: rest => .union expression (unions rest)

noncomputable def iUnion [Fintype Index] (term : Index → Expression Alphabet) :
    Expression Alphabet :=
  unions ((Finset.univ.toList).map term)

@[simp] theorem accepts_all (word : List Alphabet) : all.Accepts word := by
  simp [all, Accepts]

theorem accepts_contains_iff (predicate : Alphabet → Bool) (word : List Alphabet) :
    (contains predicate).Accepts word ↔ ∃ symbol ∈ word, predicate symbol = true := by
  constructor
  · rintro ⟨initial, rest, rfl, -, middle, final, hrest, hletter, -⟩
    obtain ⟨symbol, rfl, hsymbol⟩ := hletter
    subst rest
    exact ⟨symbol, by simp, hsymbol⟩
  · rintro ⟨symbol, hsymbol, hpredicate⟩
    obtain ⟨initial, final, rfl⟩ := List.mem_iff_append.mp hsymbol
    exact ⟨initial, symbol :: final, rfl, accepts_all _, [symbol], final, rfl,
      ⟨symbol, rfl, hpredicate⟩, accepts_all _⟩

theorem accepts_over_iff (predicate : Alphabet → Bool) (word : List Alphabet) :
    (over predicate).Accepts word ↔ ∀ symbol ∈ word, predicate symbol = true := by
  simp only [over, Accepts, accepts_contains_iff]
  constructor
  · intro h symbol hsymbol
    by_contra hfalse
    have hpfalse : predicate symbol = false := Bool.eq_false_of_not_eq_true hfalse
    exact h ⟨symbol, hsymbol, by simp [hpfalse]⟩
  · intro h hall
    obtain ⟨symbol, hsymbol, hfalse⟩ := hall
    have hpfalse : predicate symbol = false := by simpa using hfalse
    exact Bool.false_ne_true (hpfalse.symm.trans (h symbol hsymbol))

theorem accepts_iUnion_iff [Fintype Index] (term : Index → Expression Alphabet)
    (word : List Alphabet) :
    (iUnion term).Accepts word ↔ ∃ index, (term index).Accepts word := by
  classical
  have accepts_unions : ∀ expressions : List (Expression Alphabet),
      (unions expressions).Accepts word ↔
        ∃ expression ∈ expressions, expression.Accepts word := by
    intro expressions
    induction expressions with
    | nil => simp [unions, Accepts]
    | cons expression rest ih => simp [unions, Accepts, ih]
  rw [iUnion, accepts_unions]
  simp

private noncomputable def rangePredicate [Fintype Source] [DecidableEq Target]
    (encode : Source → Target) : Target → Bool :=
  fun target => decide (∃ source, encode source = target)

private theorem exists_map_of_forall_range [Fintype Source] [DecidableEq Target]
    (encode : Source → Target) (word : List Target)
    (hword : ∀ target ∈ word, ∃ source, encode source = target) :
    ∃ sourceWord : List Source, sourceWord.map encode = word := by
  induction word with
  | nil => exact ⟨[], rfl⟩
  | cons target rest ih =>
      obtain ⟨source, hsource⟩ := hword target (by simp)
      obtain ⟨sourceRest, hrest⟩ := ih (by
        intro item hitem
        exact hword item (by simp [hitem]))
      exact ⟨source :: sourceRest, by simp [hsource, hrest]⟩

private theorem accepts_over_range_iff [Fintype Source] [DecidableEq Target]
    (encode : Source → Target) (word : List Target) :
    (over (rangePredicate encode)).Accepts word ↔
      ∃ sourceWord : List Source, sourceWord.map encode = word := by
  rw [accepts_over_iff]
  constructor
  · intro h
    apply exists_map_of_forall_range encode word
    intro target htarget
    have := h target htarget
    simpa [rangePredicate] using this
  · rintro ⟨sourceWord, rfl⟩ target htarget
    simp only [List.mem_map] at htarget
    obtain ⟨source, -, rfl⟩ := htarget
    simp [rangePredicate]

/-- Injective changes of alphabet preserve star-freeness.  Complementation is
relativized to words over the image alphabet, which is itself star-free. -/
theorem exists_image [Fintype Source] [DecidableEq Target]
    (encode : Source → Target) (hinjective : Function.Injective encode)
    (expression : Expression Source) :
    ∃ image : Expression Target, ∀ word : List Target,
      image.Accepts word ↔ ∃ sourceWord : List Source,
        sourceWord.map encode = word ∧ expression.Accepts sourceWord := by
  classical
  induction expression with
  | empty =>
      refine ⟨.empty, ?_⟩
      simp [Accepts]
  | epsilon =>
      refine ⟨.epsilon, ?_⟩
      intro word
      constructor
      · intro h
        exact ⟨[], by simpa [Accepts] using h, by simp [Accepts]⟩
      · rintro ⟨sourceWord, hmap, hsource⟩
        subst sourceWord
        simpa [Accepts] using hmap.symm
  | letter predicate =>
      let imagePredicate : Target → Bool := fun target =>
        decide (∃ source, encode source = target ∧ predicate source = true)
      refine ⟨.letter imagePredicate, ?_⟩
      intro word
      constructor
      · rintro ⟨target, rfl, htarget⟩
        simp only [imagePredicate, decide_eq_true_eq] at htarget
        obtain ⟨source, rfl, hsource⟩ := htarget
        exact ⟨[source], rfl, source, rfl, hsource⟩
      · rintro ⟨sourceWord, rfl, source, hsingle, hsource⟩
        subst sourceWord
        refine ⟨encode source, rfl, ?_⟩
        change decide (∃ source', encode source' = encode source ∧
          predicate source' = true) = true
        exact decide_eq_true ⟨source, rfl, hsource⟩
  | union left right ihLeft ihRight =>
      obtain ⟨leftImage, hleft⟩ := ihLeft
      obtain ⟨rightImage, hright⟩ := ihRight
      refine ⟨.union leftImage rightImage, ?_⟩
      intro word
      simp only [Accepts, hleft, hright]
      aesop
  | inter left right ihLeft ihRight =>
      obtain ⟨leftImage, hleft⟩ := ihLeft
      obtain ⟨rightImage, hright⟩ := ihRight
      refine ⟨.inter leftImage rightImage, ?_⟩
      intro word
      simp only [Accepts, hleft, hright]
      constructor
      · rintro ⟨⟨leftWord, hleftMap, hleftAccepts⟩,
          ⟨rightWord, hrightMap, hrightAccepts⟩⟩
        have : leftWord = rightWord := hinjective.list_map
          (hleftMap.trans hrightMap.symm)
        subst rightWord
        exact ⟨leftWord, hleftMap, hleftAccepts, hrightAccepts⟩
      · rintro ⟨sourceWord, hmap, hleftAccepts, hrightAccepts⟩
        exact ⟨⟨sourceWord, hmap, hleftAccepts⟩,
          ⟨sourceWord, hmap, hrightAccepts⟩⟩
  | compl body ih =>
      obtain ⟨bodyImage, hbody⟩ := ih
      refine ⟨.inter (over (rangePredicate encode)) (.compl bodyImage), ?_⟩
      intro word
      simp only [Accepts, accepts_over_range_iff, hbody]
      constructor
      · rintro ⟨⟨sourceWord, hmap⟩, hnot⟩
        refine ⟨sourceWord, hmap, ?_⟩
        intro hsource
        exact hnot ⟨sourceWord, hmap, hsource⟩
      · rintro ⟨sourceWord, hmap, hnot⟩
        refine ⟨⟨sourceWord, hmap⟩, ?_⟩
        rintro ⟨otherWord, hotherMap, hother⟩
        have : otherWord = sourceWord := hinjective.list_map
          (hotherMap.trans hmap.symm)
        exact hnot (this ▸ hother)
  | concat left right ihLeft ihRight =>
      obtain ⟨leftImage, hleft⟩ := ihLeft
      obtain ⟨rightImage, hright⟩ := ihRight
      refine ⟨.concat leftImage rightImage, ?_⟩
      intro word
      simp only [Accepts, hleft, hright]
      constructor
      · rintro ⟨initial, final, rfl, ⟨leftWord, hleftMap, hleftAccepts⟩,
          ⟨rightWord, hrightMap, hrightAccepts⟩⟩
        refine ⟨leftWord ++ rightWord, by simp [hleftMap, hrightMap],
          leftWord, rightWord, rfl, hleftAccepts, hrightAccepts⟩
      · rintro ⟨sourceWord, rfl, leftWord, rightWord, hsplit,
          hleftAccepts, hrightAccepts⟩
        subst sourceWord
        exact ⟨leftWord.map encode, rightWord.map encode, by simp,
          ⟨leftWord, rfl, hleftAccepts⟩, ⟨rightWord, rfl, hrightAccepts⟩⟩

/-- `Substitutes replacement source target` says that `target` is obtained by
replacing each source letter by a word in its replacement language. -/
inductive Substitutes (replacement : Source → Expression Target) :
    List Source → List Target → Prop
  | nil : Substitutes replacement [] []
  | cons {symbol sourceRest piece targetRest}
      (hpiece : (replacement symbol).Accepts piece)
      (hrest : Substitutes replacement sourceRest targetRest) :
      Substitutes replacement (symbol :: sourceRest) (piece ++ targetRest)

namespace Substitutes

theorem append {replacement : Source → Expression Target}
    {leftSource rightSource : List Source} {leftTarget rightTarget : List Target}
    (hleft : Substitutes replacement leftSource leftTarget)
    (hright : Substitutes replacement rightSource rightTarget) :
    Substitutes replacement (leftSource ++ rightSource) (leftTarget ++ rightTarget) := by
  induction hleft with
  | nil => simpa using hright
  | cons hpiece _ ih =>
      simpa [List.append_assoc] using Substitutes.cons hpiece ih

theorem split {replacement : Source → Expression Target}
    {leftSource rightSource : List Source} {target : List Target}
    (h : Substitutes replacement (leftSource ++ rightSource) target) :
    ∃ leftTarget rightTarget,
      target = leftTarget ++ rightTarget ∧
      Substitutes replacement leftSource leftTarget ∧
      Substitutes replacement rightSource rightTarget := by
  induction leftSource generalizing target with
  | nil => exact ⟨[], target, rfl, .nil, by simpa using h⟩
  | cons symbol rest ih =>
      cases h with
      | cons hpiece htail =>
          obtain ⟨leftTarget, rightTarget, rfl, hleft, hright⟩ := ih htail
          exact ⟨_ , rightTarget, by simp [List.append_assoc],
            .cons hpiece hleft, hright⟩

end Substitutes

private noncomputable def substitutedLetter [Fintype Source]
    (replacement : Source → Expression Target) (predicate : Source → Bool) :
    Expression Target :=
  iUnion fun source => if predicate source then replacement source else .empty

private theorem accepts_substitutedLetter_iff [Fintype Source]
    (replacement : Source → Expression Target) (predicate : Source → Bool)
    (word : List Target) :
    (substitutedLetter replacement predicate).Accepts word ↔
      ∃ source, predicate source = true ∧ (replacement source).Accepts word := by
  classical
  rw [substitutedLetter, accepts_iUnion_iff]
  constructor
  · rintro ⟨source, hsource⟩
    by_cases hpredicate : predicate source = true
    · exact ⟨source, hpredicate, by simpa [hpredicate] using hsource⟩
    · simp [hpredicate, Accepts] at hsource
  · rintro ⟨source, hpredicate, hsource⟩
    exact ⟨source, by simpa [hpredicate] using hsource⟩

/-- Inverse images under a uniquely decipherable star-free substitution are
star-free.  `domain` recognizes exactly all encoded words. -/
theorem exists_inverse_substitution [Fintype Source]
    (replacement : Source → Expression Target) (domain : Expression Target)
    (hdomain : ∀ targetWord,
      domain.Accepts targetWord ↔ ∃ sourceWord,
        Substitutes replacement sourceWord targetWord)
    (hfunctional : ∀ {left right targetWord},
      Substitutes replacement left targetWord →
      Substitutes replacement right targetWord → left = right)
    (expression : Expression Source) :
    ∃ inverse : Expression Target, ∀ targetWord,
      inverse.Accepts targetWord ↔ ∃ sourceWord,
        Substitutes replacement sourceWord targetWord ∧
        expression.Accepts sourceWord := by
  classical
  induction expression with
  | empty =>
      refine ⟨.empty, ?_⟩
      simp [Accepts]
  | epsilon =>
      refine ⟨.epsilon, ?_⟩
      intro targetWord
      constructor
      · intro h
        have : targetWord = [] := h
        subst targetWord
        exact ⟨[], .nil, rfl⟩
      · rintro ⟨sourceWord, hsubstitution, hsource⟩
        subst sourceWord
        cases hsubstitution
        rfl
  | letter predicate =>
      refine ⟨substitutedLetter replacement predicate, ?_⟩
      intro targetWord
      rw [accepts_substitutedLetter_iff]
      constructor
      · rintro ⟨source, hpredicate, hreplacement⟩
        refine ⟨[source], ?_, source, rfl, hpredicate⟩
        simpa using Substitutes.cons hreplacement Substitutes.nil
      · rintro ⟨sourceWord, hsubstitution, source, hsourceWord, hpredicate⟩
        subst sourceWord
        cases hsubstitution with
        | cons hpiece hrest =>
            cases hrest
            simpa using ⟨source, hpredicate, hpiece⟩
  | union left right ihLeft ihRight =>
      obtain ⟨leftInverse, hleft⟩ := ihLeft
      obtain ⟨rightInverse, hright⟩ := ihRight
      refine ⟨.union leftInverse rightInverse, ?_⟩
      intro targetWord
      simp only [Accepts, hleft, hright]
      aesop
  | inter left right ihLeft ihRight =>
      obtain ⟨leftInverse, hleft⟩ := ihLeft
      obtain ⟨rightInverse, hright⟩ := ihRight
      refine ⟨.inter leftInverse rightInverse, ?_⟩
      intro targetWord
      simp only [Accepts, hleft, hright]
      constructor
      · rintro ⟨⟨leftWord, hleftSub, hleftAccepts⟩,
          ⟨rightWord, hrightSub, hrightAccepts⟩⟩
        have : leftWord = rightWord := hfunctional hleftSub hrightSub
        subst rightWord
        exact ⟨leftWord, hleftSub, hleftAccepts, hrightAccepts⟩
      · rintro ⟨sourceWord, hsub, hleftAccepts, hrightAccepts⟩
        exact ⟨⟨sourceWord, hsub, hleftAccepts⟩,
          ⟨sourceWord, hsub, hrightAccepts⟩⟩
  | compl body ih =>
      obtain ⟨bodyInverse, hbody⟩ := ih
      refine ⟨.inter domain (.compl bodyInverse), ?_⟩
      intro targetWord
      simp only [Accepts, hdomain, hbody]
      constructor
      · rintro ⟨⟨sourceWord, hsub⟩, hnot⟩
        refine ⟨sourceWord, hsub, ?_⟩
        intro hbodyAccepts
        exact hnot ⟨sourceWord, hsub, hbodyAccepts⟩
      · rintro ⟨sourceWord, hsub, hnot⟩
        refine ⟨⟨sourceWord, hsub⟩, ?_⟩
        rintro ⟨otherWord, hotherSub, hotherAccepts⟩
        exact hnot ((hfunctional hotherSub hsub) ▸ hotherAccepts)
  | concat left right ihLeft ihRight =>
      obtain ⟨leftInverse, hleft⟩ := ihLeft
      obtain ⟨rightInverse, hright⟩ := ihRight
      refine ⟨.concat leftInverse rightInverse, ?_⟩
      intro targetWord
      simp only [Accepts, hleft, hright]
      constructor
      · rintro ⟨leftTarget, rightTarget, rfl,
          ⟨leftSource, hleftSub, hleftAccepts⟩,
          ⟨rightSource, hrightSub, hrightAccepts⟩⟩
        exact ⟨leftSource ++ rightSource, hleftSub.append hrightSub,
          leftSource, rightSource, rfl, hleftAccepts, hrightAccepts⟩
      · rintro ⟨sourceWord, hsub, leftSource, rightSource, rfl,
          hleftAccepts, hrightAccepts⟩
        obtain ⟨leftTarget, rightTarget, rfl, hleftSub, hrightSub⟩ := hsub.split
        exact ⟨leftTarget, rightTarget, rfl,
          ⟨leftSource, hleftSub, hleftAccepts⟩,
          ⟨rightSource, hrightSub, hrightAccepts⟩⟩

def delimitedDomain [DecidableEq Alphabet] (delimiter : Alphabet) :
    Expression Alphabet :=
  .union .epsilon (.concat all (.letter fun symbol => decide (symbol = delimiter)))

theorem accepts_delimitedDomain_iff [DecidableEq Alphabet]
    (delimiter : Alphabet) (word : List Alphabet) :
    (delimitedDomain delimiter).Accepts word ↔
      word = [] ∨ ∃ initial, word = initial ++ [delimiter] := by
  constructor
  · rintro (hempty | ⟨initial, final, hword, -, symbol, hfinal, hsymbol⟩)
    · exact Or.inl hempty
    · simp only [decide_eq_true_eq] at hsymbol
      subst symbol
      subst final
      exact Or.inr ⟨initial, hword⟩
  · rintro (rfl | ⟨initial, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨initial, [delimiter], rfl, accepts_all _, delimiter, rfl,
        by simp⟩

private theorem delimiter_prefix_unique [DecidableEq Alphabet]
    {delimiter : Alphabet} {left right leftRest rightRest : List Alphabet}
    (hleft : delimiter ∉ left) (hright : delimiter ∉ right)
    (heq : left ++ delimiter :: leftRest = right ++ delimiter :: rightRest) :
    left = right ∧ leftRest = rightRest := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => simpa using heq
      | cons head tail =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
          exact (hright (by simp [heq.1])).elim
  | cons head tail ih =>
      cases right with
      | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
          exact (hleft (by simp [heq.1])).elim
      | cons other otherTail =>
          simp only [List.cons_append, List.cons.injEq] at heq
          have htail : delimiter ∉ tail := fun hmem => hleft (by simp [hmem])
          have hotherTail : delimiter ∉ otherTail := fun hmem => hright (by simp [hmem])
          obtain ⟨htails, hrests⟩ := ih htail hotherTail heq.2
          exact ⟨by simp [heq.1, htails], hrests⟩

/-- Delimiter-terminated replacement languages form a uniquely decipherable
code, and their concatenations are exactly the empty word and the words ending
in the delimiter. -/
theorem delimited_substitution [DecidableEq Target]
    (delimiter : Target) (label : List Target → Source)
    (replacement : Source → Expression Target)
    (hreplacement : ∀ source word,
      (replacement source).Accepts word ↔
        ∃ chunk, delimiter ∉ chunk ∧ word = chunk ++ [delimiter] ∧
          label chunk = source) :
    (∀ targetWord,
      (delimitedDomain delimiter).Accepts targetWord ↔
        ∃ sourceWord, Substitutes replacement sourceWord targetWord) ∧
    (∀ {left right targetWord},
      Substitutes replacement left targetWord →
      Substitutes replacement right targetWord → left = right) := by
  constructor
  · intro targetWord
    rw [accepts_delimitedDomain_iff]
    constructor
    · rintro (rfl | ⟨initial, rfl⟩)
      · exact ⟨[], .nil⟩
      · have parsePrefix : ∀ word : List Target,
            ∃ sourceWord encoded chunk,
              word = encoded ++ chunk ∧
              Substitutes replacement sourceWord encoded ∧
              delimiter ∉ chunk := by
          intro word
          induction word using List.reverseRecOn with
          | nil => exact ⟨[], [], [], rfl, .nil, by simp⟩
          | append_singleton word symbol ih =>
              obtain ⟨sourceWord, encoded, chunk, hword, hsub, hchunk⟩ := ih
              by_cases hsymbol : symbol = delimiter
              · subst symbol
                have hpiece : (replacement (label chunk)).Accepts
                    (chunk ++ [delimiter]) :=
                  (hreplacement _ _).2 ⟨chunk, hchunk, rfl, rfl⟩
                have hone : Substitutes replacement [label chunk]
                    (chunk ++ [delimiter]) := by
                  simpa using Substitutes.cons hpiece Substitutes.nil
                refine ⟨sourceWord ++ [label chunk],
                  encoded ++ chunk ++ [delimiter], [], ?_, ?_, by simp⟩
                · simp [hword, List.append_assoc]
                · simpa [List.append_assoc] using hsub.append hone
              · refine ⟨sourceWord, encoded, chunk ++ [symbol], ?_, hsub, ?_⟩
                · simp [hword, List.append_assoc]
                · intro hmem
                  rw [List.mem_append, List.mem_singleton] at hmem
                  exact hmem.elim hchunk (fun heq => hsymbol heq.symm)
        obtain ⟨sourceWord, encoded, chunk, hinitial, hsub, hchunk⟩ :=
          parsePrefix initial
        have hpiece : (replacement (label chunk)).Accepts
            (chunk ++ [delimiter]) :=
          (hreplacement _ _).2 ⟨chunk, hchunk, rfl, rfl⟩
        have hone : Substitutes replacement [label chunk]
            (chunk ++ [delimiter]) := by
          simpa using Substitutes.cons hpiece Substitutes.nil
        refine ⟨sourceWord ++ [label chunk], ?_⟩
        simpa [hinitial, List.append_assoc] using hsub.append hone
    · rintro ⟨sourceWord, hsub⟩
      have substitutionEnds : ∀ {sourceWord : List Source} {word : List Target},
          Substitutes replacement sourceWord word →
            word = [] ∨ ∃ initial, word = initial ++ [delimiter] := by
        intro source word h
        induction h with
        | nil => exact Or.inl rfl
        | @cons symbol sourceRest piece targetRest hpiece hrest ih =>
            obtain ⟨chunk, -, hpieceShape, -⟩ := (hreplacement _ _).1 hpiece
            right
            rcases ih with rfl | ⟨initial, rfl⟩
            · exact ⟨chunk, by simpa using hpieceShape⟩
            · exact ⟨piece ++ initial, by simp⟩
      exact substitutionEnds hsub
  · have substitutes_nil_iff : ∀ word,
        Substitutes replacement [] word ↔ word = [] := by
      intro word
      constructor
      · intro h
        cases h
        rfl
      · rintro rfl
        exact .nil
    have substitutes_cons_iff : ∀ symbol sourceRest word,
        Substitutes replacement (symbol :: sourceRest) word ↔
          ∃ piece targetRest, word = piece ++ targetRest ∧
            (replacement symbol).Accepts piece ∧
            Substitutes replacement sourceRest targetRest := by
      intro symbol sourceRest word
      constructor
      · intro h
        cases h with
        | cons hpiece hrest => exact ⟨_, _, rfl, hpiece, hrest⟩
      · rintro ⟨piece, targetRest, rfl, hpiece, hrest⟩
        exact .cons hpiece hrest
    have source_nil_of_target_nil : ∀ sourceWord,
        Substitutes replacement sourceWord [] → sourceWord = [] := by
      intro sourceWord hsub
      cases sourceWord with
      | nil => rfl
      | cons symbol sourceRest =>
          obtain ⟨piece, targetRest, hempty, hpiece, -⟩ :=
            (substitutes_cons_iff _ _ _).1 hsub
          obtain ⟨chunk, -, hshape, -⟩ := (hreplacement _ _).1 hpiece
          have : piece = [] := List.append_eq_nil_iff.mp hempty.symm |>.1
          simp [this] at hshape
    intro left
    induction left with
    | nil =>
        intro right targetWord hleft hright
        have htarget : targetWord = [] := (substitutes_nil_iff _).1 hleft
        subst targetWord
        exact (source_nil_of_target_nil right hright).symm
    | cons leftSymbol leftRest ih =>
        intro right targetWord hleft hright
        cases right with
        | nil =>
            have htarget : targetWord = [] := (substitutes_nil_iff _).1 hright
            subst targetWord
            exact (List.cons_ne_nil leftSymbol leftRest
              (source_nil_of_target_nil _ hleft)).elim
        | cons rightSymbol rightRest =>
            obtain ⟨leftPiece, leftTarget, hleftTarget, hleftPiece, hleftRest⟩ :=
              (substitutes_cons_iff _ _ _).1 hleft
            obtain ⟨rightPiece, rightTarget, hrightTarget, hrightPiece, hrightRest⟩ :=
              (substitutes_cons_iff _ _ _).1 hright
            obtain ⟨leftChunk, hleftChunk, hleftShape, hleftLabel⟩ :=
              (hreplacement _ _).1 hleftPiece
            obtain ⟨rightChunk, hrightChunk, hrightShape, hrightLabel⟩ :=
              (hreplacement _ _).1 hrightPiece
            have heq : leftChunk ++ delimiter :: leftTarget =
                rightChunk ++ delimiter :: rightTarget := by
              have hraw : leftPiece ++ leftTarget = rightPiece ++ rightTarget :=
                hleftTarget.symm.trans hrightTarget
              rw [hleftShape, hrightShape] at hraw
              simpa [List.append_assoc] using hraw
            obtain ⟨hchunks, htargets⟩ :=
              delimiter_prefix_unique hleftChunk hrightChunk heq
            have hsymbols : leftSymbol = rightSymbol := by
              rw [← hleftLabel, ← hrightLabel, hchunks]
            subst rightSymbol
            congr
            exact ih hleftRest (htargets ▸ hrightRest)

end Expression

/-! ## The local-divisor proof of Schützenberger's theorem -/

def wordEval [Monoid M] (letter : Alphabet → M) (word : List Alphabet) : M :=
  (word.map letter).prod

@[simp] theorem wordEval_nil [Monoid M] (letter : Alphabet → M) :
    wordEval letter [] = 1 := rfl

@[simp] theorem wordEval_cons [Monoid M] (letter : Alphabet → M)
    (head : Alphabet) (tail : List Alphabet) :
    wordEval letter (head :: tail) = letter head * wordEval letter tail := by
  simp [wordEval]

@[simp] theorem wordEval_append [Monoid M] (letter : Alphabet → M)
    (left right : List Alphabet) :
    wordEval letter (left ++ right) = wordEval letter left * wordEval letter right := by
  simp [wordEval]

@[simp] theorem wordEval_map [Monoid M] (letter : Alphabet → M)
    (encode : Source → Alphabet) (word : List Source) :
    wordEval letter (word.map encode) = wordEval (fun source => letter (encode source)) word := by
  induction word with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem split_first [DecidableEq Alphabet] (delimiter : Alphabet) :
    ∀ word : List Alphabet,
      delimiter ∉ word ∨ ∃ initial final,
        delimiter ∉ initial ∧ word = initial ++ delimiter :: final := by
  intro word
  induction word with
  | nil => exact Or.inl (by simp)
  | cons head tail ih =>
      by_cases hhead : head = delimiter
      · subst head
        exact Or.inr ⟨[], tail, by simp, rfl⟩
      · rcases ih with htail | ⟨initial, final, hinitial, htail⟩
        · exact Or.inl (by simp [hhead, Ne.symm hhead, htail])
        · exact Or.inr ⟨head :: initial, final,
            by simp [hhead, Ne.symm hhead, hinitial],
            by simp [htail]⟩

private theorem split_last [DecidableEq Alphabet] (delimiter : Alphabet) :
    ∀ word : List Alphabet,
      delimiter ∉ word ∨ ∃ initial final,
        delimiter ∉ final ∧ word = initial ++ delimiter :: final := by
  intro word
  induction word using List.reverseRecOn with
  | nil => exact Or.inl (by simp)
  | append_singleton initial last ih =>
      by_cases hlast : last = delimiter
      · subst last
        exact Or.inr ⟨initial, [], by simp, by simp⟩
      · rcases ih with hinitial | ⟨before, after, hafter, hinitial⟩
        · exact Or.inl (by simp [hinitial, hlast, Ne.symm hlast])
        · exact Or.inr ⟨before, after ++ [last],
            by simp [hafter, hlast, Ne.symm hlast],
            by simp [hinitial, List.append_assoc]⟩

structure FiberExpressions (Alphabet M : Type*) [Monoid M]
    (letter : Alphabet → M) where
  expression : M → Expression Alphabet
  correct : ∀ target word,
    (expression target).Accepts word ↔ wordEval letter word = target

/-- Schützenberger's theorem in the constructive form needed here: every
fiber of a morphism into a finite aperiodic monoid has an explicit star-free
expression.  The proof is the local-divisor induction on monoid size and
alphabet size. -/
theorem exists_aperiodic_fiberExpressions {Alphabet M : Type u}
    [Fintype Alphabet] [Fintype M] [Monoid M]
    (letter : Alphabet → M) (hM : IsAperiodic M) :
    Nonempty (FiberExpressions Alphabet M letter) := by
  classical
  induction hcardM : Fintype.card M using Nat.strong_induction_on generalizing M Alphabet with
  | h sizeM outer =>
      induction hcardA : Fintype.card Alphabet using Nat.strong_induction_on
          generalizing Alphabet with
      | h sizeA inner =>
          by_cases hall : ∀ symbol, letter symbol = 1
          · have heval : ∀ word, wordEval letter word = 1 := by
              intro word
              induction word with
              | nil => rfl
              | cons head tail ih => simp [hall head, ih]
            let family : M → Expression Alphabet := fun target =>
              if target = 1 then Expression.all else .empty
            refine ⟨⟨family, ?_⟩⟩
            intro target word
            by_cases htarget : target = 1
            · subst target
              simp [family, Expression.accepts_all, heval]
            · simp [family, htarget, Expression.Accepts, heval, Ne.symm htarget]
          · push_neg at hall
            obtain ⟨delimiter, hdelimiter⟩ := hall
            let SmallerAlphabet := {symbol : Alphabet // symbol ≠ delimiter}
            let smallerLetter : SmallerAlphabet → M :=
              fun symbol => letter symbol.val
            have hsmallerCard : Fintype.card SmallerAlphabet < Fintype.card Alphabet := by
              apply Fintype.card_lt_of_injective_of_not_mem
                (fun symbol : SmallerAlphabet => symbol.val) Subtype.val_injective
                (b := delimiter)
              rintro ⟨symbol, hsymbol⟩
              exact symbol.property hsymbol
            obtain ⟨smaller⟩ :=
              inner (Fintype.card SmallerAlphabet) (by simpa [hcardA] using hsmallerCard)
                smallerLetter rfl
            have himage : ∀ target : M, ∃ image : Expression Alphabet,
                ∀ word : List Alphabet,
                  image.Accepts word ↔ ∃ sourceWord : List SmallerAlphabet,
                    sourceWord.map Subtype.val = word ∧
                    (smaller.expression target).Accepts sourceWord := by
              intro target
              exact Expression.exists_image (fun symbol : SmallerAlphabet => symbol.val)
                Subtype.val_injective (smaller.expression target)
            let base : M → Expression Alphabet := fun target =>
              Classical.choose (himage target)
            have hbaseImage : ∀ target word,
                (base target).Accepts word ↔ ∃ sourceWord : List SmallerAlphabet,
                  sourceWord.map Subtype.val = word ∧
                  (smaller.expression target).Accepts sourceWord := by
              intro target
              exact Classical.choose_spec (himage target)
            have hbase : ∀ target word,
                (base target).Accepts word ↔
                  delimiter ∉ word ∧ wordEval letter word = target := by
              intro target word
              constructor
              · intro h
                obtain ⟨sourceWord, rfl, hsource⟩ := (hbaseImage target word).1 h
                constructor
                · intro hmem
                  simp only [List.mem_map] at hmem
                  obtain ⟨symbol, -, hsymbol⟩ := hmem
                  exact symbol.property hsymbol
                · rw [smaller.correct] at hsource
                  rw [wordEval_map]
                  exact hsource
              · rintro ⟨hnotmem, heval⟩
                have hrange : ∀ symbol ∈ word,
                    ∃ source : SmallerAlphabet, source.val = symbol := by
                  intro symbol hsymbol
                  exact ⟨⟨symbol, fun heq => hnotmem (heq ▸ hsymbol)⟩, rfl⟩
                obtain ⟨sourceWord, hsourceWord⟩ :=
                  Expression.exists_map_of_forall_range
                    (fun source : SmallerAlphabet => source.val) word hrange
                apply (hbaseImage target word).2
                refine ⟨sourceWord, hsourceWord, ?_⟩
                rw [smaller.correct]
                calc
                  wordEval smallerLetter sourceWord =
                      wordEval letter (sourceWord.map Subtype.val) := by
                    symm
                    exact wordEval_map letter Subtype.val sourceWord
                  _ = wordEval letter word := by rw [hsourceWord]
                  _ = target := heval
            let delimiterLetter : Expression Alphabet :=
              .letter fun symbol => decide (symbol = delimiter)
            let replacement : M → Expression Alphabet := fun target =>
              .concat (base target) delimiterLetter
            have hreplacement : ∀ target word,
                (replacement target).Accepts word ↔
                  ∃ chunk, delimiter ∉ chunk ∧
                    word = chunk ++ [delimiter] ∧ wordEval letter chunk = target := by
              intro target word
              constructor
              · rintro ⟨chunk, ending, hword, hchunk, symbol, hending, hsymbol⟩
                simp only [delimiterLetter, decide_eq_true_eq] at hsymbol
                subst symbol
                subst ending
                obtain ⟨hnotmem, heval⟩ := (hbase target chunk).1 hchunk
                exact ⟨chunk, hnotmem, hword, heval⟩
              · rintro ⟨chunk, hnotmem, rfl, heval⟩
                exact ⟨chunk, [delimiter], rfl, (hbase target chunk).2
                  ⟨hnotmem, heval⟩, delimiter, rfl, by simp [delimiterLetter]⟩
            let Local := LocalDivisor M (letter delimiter)
            let sandwich : M → Local := fun value =>
              ⟨letter delimiter * value * letter delimiter,
                ⟨value * letter delimiter, by simp [mul_assoc]⟩,
                ⟨letter delimiter * value, rfl⟩⟩
            have hlocalCard : Fintype.card Local < Fintype.card M :=
              LocalDivisor.card_lt hM hdelimiter
            have hlocalAperiodic : IsAperiodic Local := LocalDivisor.isAperiodic hM
            obtain ⟨localCertificate⟩ :=
              outer (Fintype.card Local) (by simpa [hcardM] using hlocalCard)
                sandwich hlocalAperiodic rfl
            obtain ⟨hdomain, hfunctional⟩ :=
              Expression.delimited_substitution delimiter (wordEval letter)
                replacement hreplacement
            have hinverse : ∀ target : Local, ∃ inverse : Expression Alphabet,
                ∀ word : List Alphabet,
                  inverse.Accepts word ↔ ∃ sourceWord : List M,
                    Expression.Substitutes replacement sourceWord word ∧
                    (localCertificate.expression target).Accepts sourceWord := by
              intro target
              exact Expression.exists_inverse_substitution replacement
                (Expression.delimitedDomain delimiter) hdomain hfunctional
                (localCertificate.expression target)
            let inverse : Local → Expression Alphabet := fun target =>
              Classical.choose (hinverse target)
            have hinverseCorrect : ∀ target word,
                (inverse target).Accepts word ↔ ∃ sourceWord : List M,
                  Expression.Substitutes replacement sourceWord word ∧
                  wordEval sandwich sourceWord = target := by
              intro target word
              rw [show inverse target = Classical.choose (hinverse target) by rfl,
                Classical.choose_spec (hinverse target)]
              constructor
              · rintro ⟨sourceWord, hsub, haccepts⟩
                exact ⟨sourceWord, hsub,
                  (localCertificate.correct target sourceWord).1 haccepts⟩
              · rintro ⟨sourceWord, hsub, heval⟩
                exact ⟨sourceWord, hsub,
                  (localCertificate.correct target sourceWord).2 heval⟩
            have hsubstitutionEval : ∀ {sourceWord : List M} {word : List Alphabet},
                Expression.Substitutes replacement sourceWord word →
                  (wordEval sandwich sourceWord).value =
                    letter delimiter * wordEval letter word := by
              intro sourceWord word hsub
              induction hsub with
              | nil => simp [sandwich]
              | @cons symbol sourceRest piece targetRest hpiece hrest ih =>
                  obtain ⟨chunk, -, hpieceShape, hchunkEval⟩ :=
                    (hreplacement _ _).1 hpiece
                  have hpieceEval : wordEval letter piece =
                      symbol * letter delimiter := by
                    rw [hpieceShape, wordEval_append, hchunkEval]
                    simp
                  rw [wordEval_cons, wordEval_append]
                  calc
                    (sandwich symbol * wordEval sandwich sourceRest).value =
                        (letter delimiter * symbol) * letter delimiter *
                          wordEval letter targetRest :=
                      LocalDivisor.mul_value_of_factors
                        (sandwich symbol) (wordEval sandwich sourceRest)
                        (left := letter delimiter * symbol)
                        (right := wordEval letter targetRest) rfl ih.symm
                    _ = letter delimiter *
                        (wordEval letter piece * wordEval letter targetRest) := by
                      rw [hpieceEval]
                      simp [mul_assoc]
            let middle : Local → Expression Alphabet := fun target =>
              .concat delimiterLetter (inverse target)
            have hmiddleSound : ∀ target word,
                (middle target).Accepts word → wordEval letter word = target.value := by
              intro target word
              rintro ⟨beginning, tail, rfl, hbeginning, hinv⟩
              obtain ⟨symbol, hbeginning, hsymbol⟩ := hbeginning
              simp only [delimiterLetter, decide_eq_true_eq] at hsymbol
              subst symbol
              subst beginning
              obtain ⟨sourceWord, hsub, heval⟩ :=
                (hinverseCorrect target tail).1 hinv
              have hvalue : target.value =
                  letter delimiter * wordEval letter tail := by
                rw [← heval]
                exact hsubstitutionEval hsub
              rw [wordEval_append]
              simpa using hvalue.symm
            have hmiddleComplete : ∀ tail,
                (Expression.delimitedDomain delimiter).Accepts tail →
                  ∃ target : Local,
                    (middle target).Accepts ([delimiter] ++ tail) := by
              intro tail htail
              obtain ⟨sourceWord, hsub⟩ := (hdomain tail).1 htail
              let target : Local := wordEval sandwich sourceWord
              refine ⟨target, [delimiter], tail, rfl, ?_, ?_⟩
              · exact ⟨delimiter, rfl, by simp [delimiterLetter]⟩
              · apply (hinverseCorrect target tail).2
                exact ⟨sourceWord, hsub, rfl⟩
            let combined : M → Expression Alphabet := fun target =>
              .union (base target)
                (Expression.iUnion fun index : M × Local × M =>
                  if index.1 * (index.2.1.value * index.2.2) = target then
                    .concat (base index.1)
                      (.concat (middle index.2.1) (base index.2.2))
                  else .empty)
            refine ⟨⟨combined, ?_⟩⟩
            intro target word
            constructor
            · intro haccepts
              rcases haccepts with hbaseAccepts | hunion
              · exact (hbase target word).1 hbaseAccepts |>.2
              · rw [Expression.accepts_iUnion_iff] at hunion
                obtain ⟨index, hindex⟩ := hunion
                split at hindex
                next hproduct =>
                  obtain ⟨initial, rest, rfl, hinitial, central, suffix, rfl,
                    hcentral, hsuffix⟩ := hindex
                  obtain ⟨-, hinitialEval⟩ := (hbase index.1 initial).1 hinitial
                  obtain ⟨-, hsuffixEval⟩ :=
                    (hbase index.2.2 suffix).1 hsuffix
                  rw [wordEval_append, wordEval_append, hinitialEval,
                    hmiddleSound index.2.1 central hcentral, hsuffixEval]
                  exact hproduct
                next hproduct => exact hindex.elim
            · intro heval
              rcases split_first delimiter word with hnone |
                  ⟨initial, afterFirst, hinitial, hword⟩
              · exact Or.inl ((hbase target word).2 ⟨hnone, heval⟩)
              · have decomposition : ∃ tail suffix,
                    delimiter ∉ suffix ∧
                    afterFirst = tail ++ suffix ∧
                    (Expression.delimitedDomain delimiter).Accepts tail := by
                    rcases split_last delimiter afterFirst with hnoneLast |
                        ⟨inside, suffix, hsuffix, hafter⟩
                    · exact ⟨[], afterFirst, hnoneLast, by simp,
                        (Expression.accepts_delimitedDomain_iff _ _).2 (Or.inl rfl)⟩
                    · refine ⟨inside ++ [delimiter], suffix, hsuffix, ?_, ?_⟩
                      · simpa [List.append_assoc] using hafter
                      · apply (Expression.accepts_delimitedDomain_iff _ _).2
                        exact Or.inr ⟨inside, rfl⟩
                obtain ⟨tail, suffix, hsuffix, hafter, htail⟩ := decomposition
                obtain ⟨middleTarget, hmiddle⟩ := hmiddleComplete tail htail
                let initialTarget := wordEval letter initial
                let suffixTarget := wordEval letter suffix
                have hwordComplete : word =
                    initial ++ (([delimiter] ++ tail) ++ suffix) := by
                  simp [hword, hafter, List.append_assoc]
                have hcentralEval : wordEval letter ([delimiter] ++ tail) =
                    middleTarget.value :=
                  hmiddleSound middleTarget ([delimiter] ++ tail) hmiddle
                have hproduct : initialTarget *
                    (middleTarget.value * suffixTarget) = target := by
                  rw [← heval, hwordComplete, wordEval_append, wordEval_append,
                    hcentralEval]
                right
                apply (Expression.accepts_iUnion_iff _ word).2
                refine ⟨(initialTarget, middleTarget, suffixTarget), ?_⟩
                simp only [hproduct, if_true, Expression.Accepts]
                refine ⟨initial, [delimiter] ++ tail ++ suffix, ?_, ?_,
                  [delimiter] ++ tail, suffix, rfl, hmiddle, ?_⟩
                · simp [hword, hafter, List.append_assoc]
                · exact (hbase initialTarget initial).2 ⟨hinitial, rfl⟩
                · exact (hbase suffixTarget suffix).2 ⟨hsuffix, rfl⟩

/-! ## Ordered automata -/

/-- Order-preserving endomaps, multiplied in the temporal order in which an
automaton reads letters: `left * right` first applies `left`, then `right`. -/
structure OrderedEnd (State : Type*) [Preorder State] where
  toFun : State → State
  monotone : Monotone toFun

namespace OrderedEnd

instance [Preorder State] : CoeFun (OrderedEnd State) (fun _ => State → State) :=
  ⟨OrderedEnd.toFun⟩

@[ext] theorem ext [Preorder State] {left right : OrderedEnd State}
    (h : ∀ state, left state = right state) : left = right := by
  rcases left with ⟨leftFunction, leftMonotone⟩
  rcases right with ⟨rightFunction, rightMonotone⟩
  have hfunctions : leftFunction = rightFunction := funext h
  subst rightFunction
  rfl

def one [Preorder State] : OrderedEnd State := ⟨id, monotone_id⟩

def mul [Preorder State] (left right : OrderedEnd State) : OrderedEnd State :=
  ⟨fun state => right (left state), right.monotone.comp left.monotone⟩

instance [Preorder State] : Monoid (OrderedEnd State) where
  one := one
  mul := mul
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  mul_assoc _ _ _ := ext fun _ => rfl

noncomputable instance [Preorder State] [Fintype State] : Fintype (OrderedEnd State) := by
  letI : Fintype (State → State) := Fintype.ofFinite (State → State)
  exact Fintype.ofInjective OrderedEnd.toFun (fun _ _ h => ext (congrFun h))

@[simp] theorem one_apply [Preorder State] (state : State) :
    (1 : OrderedEnd State) state = state := rfl

@[simp] theorem mul_apply [Preorder State] (left right : OrderedEnd State)
    (state : State) : (left * right) state = right (left state) := rfl

theorem pow_apply [Preorder State] (transition : OrderedEnd State)
    (exponent : ℕ) (state : State) :
    (transition ^ exponent) state = (transition.toFun^[exponent]) state := by
  induction exponent with
  | zero => rfl
  | succ exponent ih =>
      rw [pow_succ, mul_apply, ih, Function.iterate_succ_apply']

private theorem orbit_has_fixed_point [LinearOrder State] [Finite State]
    (transition : OrderedEnd State) (state : State) :
    ∃ exponent, (transition.toFun^[exponent]) state =
      (transition.toFun^[exponent + 1]) state := by
  obtain ⟨left, right, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun exponent : ℕ => (transition.toFun^[exponent]) state)
  have increasing (hstart : state ≤ transition state) {i j : ℕ}
      (hij : i < j)
      (hijEq : (transition.toFun^[i]) state = (transition.toFun^[j]) state) :
      (transition.toFun^[i]) state = (transition.toFun^[i + 1]) state := by
    have hmono := transition.monotone.monotone_iterate_of_le_map hstart
    apply le_antisymm (hmono (by omega))
    calc
      (transition.toFun^[i + 1]) state ≤ (transition.toFun^[j]) state :=
        hmono (by omega)
      _ = (transition.toFun^[i]) state := hijEq.symm
  have decreasing (hstart : transition state ≤ state) {i j : ℕ}
      (hij : i < j)
      (hijEq : (transition.toFun^[i]) state = (transition.toFun^[j]) state) :
      (transition.toFun^[i]) state = (transition.toFun^[i + 1]) state := by
    have hanti := transition.monotone.antitone_iterate_of_map_le hstart
    apply le_antisymm
    · calc
        (transition.toFun^[i]) state = (transition.toFun^[j]) state := hijEq
        _ ≤ (transition.toFun^[i + 1]) state := hanti (by omega)
    · exact hanti (by omega)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨left, ?_⟩
    rcases le_total state (transition state) with hstart | hstart
    · exact increasing hstart hlt heq
    · exact decreasing hstart hlt heq
  · refine ⟨right, ?_⟩
    rcases le_total state (transition state) with hstart | hstart
    · exact increasing hstart hgt heq.symm
    · exact decreasing hstart hgt heq.symm

private theorem iterate_fixed_of_ge {State : Type u} {function : State → State} {state : State}
    {start exponent : ℕ}
    (hfixed : (function^[start]) state = (function^[start + 1]) state)
    (hle : start ≤ exponent) :
    (function^[exponent]) state = (function^[exponent + 1]) state := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction offset with
  | zero => simpa using hfixed
  | succ offset ih =>
      have ih' := ih (by omega)
      calc
        (function^[start + (offset + 1)]) state =
            function ((function^[start + offset]) state) := by
          simpa only [show start + (offset + 1) = (start + offset) + 1 by omega,
            ← Nat.succ_eq_add_one] using
              Function.iterate_succ_apply' function (start + offset) state
        _ = function ((function^[start + offset + 1]) state) := congrArg function ih'
        _ = (function^[start + (offset + 1) + 1]) state := by
          symm
          simpa only [show start + (offset + 1) + 1 =
              (start + offset + 1) + 1 by omega, ← Nat.succ_eq_add_one] using
            Function.iterate_succ_apply' function (start + offset + 1) state

/-- Every finite ordered transformation monoid is aperiodic. -/
theorem isAperiodic [LinearOrder State] [Fintype State] :
    IsAperiodic (OrderedEnd State) := by
  intro transition
  choose pointExponent hpoint using fun state => orbit_has_fixed_point transition state
  let exponent := ∑ state : State, pointExponent state
  refine ⟨exponent, ext fun state => ?_⟩
  rw [pow_apply, pow_apply]
  apply iterate_fixed_of_ge (hpoint state)
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ state)

end OrderedEnd

end OrderedAddition
