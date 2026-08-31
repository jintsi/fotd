import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.List.Palindrome

/-- Fact Of The Day 3: 31 is the only prime that is divisible by 31. -/
theorem fotd3 {p : Nat.Primes} : 31 ∣ p.val ↔ p = ⟨31, by decide⟩ :=
  (Nat.dvd_prime_two_le p.prop (by decide)).trans (by cases p; grind only)

/-- Fact Of The Day 4: You can divide a finite pizza between an infinite amount of people and they
would all get more pizza than average. -/
theorem fotd4 {pizza : ℝ} (h : 0 < pizza) : ∃ f : ℕ → ℝ, HasSum f pizza ∧ ∀ n,
    (Filter.atTop.limUnder fun n => (∑ i ∈ Finset.range n, f i) / n) < f n := by
  use fun n => pizza / 2 / 2 ^ n, hasSum_geometric_two' pizza
  intro n
  grw [← h]; apply le_of_eq; simp
  apply Filter.Tendsto.limUnder_eq
  exact (hasSum_geometric_two' pizza).tendsto_sum_nat.div_atTop tendsto_natCast_atTop_atTop

/-- Fact Of The Day 5: One of the solutions of
```
x^2 + 69x + 420 = 0
```
is approximately -6.74662183 -/
theorem fotd5 : ∃ r ∈ Set.Ioo (-6.74662183 : ℝ) (-6.74662182 : ℝ), r ^ 2 + 69 * r + 420 = 0 := by
  grw [← Set.mem_image, ← intermediate_value_Ioo]
  · norm_num
  · norm_num
  · fun_prop

/-- Fact Of The Day 6: The empty set is closed under any function, is commutative, associative and
distributive, which makes it the most perfect set. -/
theorem fotd6 {f g : α → α → α} :
    ∀ a ∈ (∅ : Set α), ∀ b ∈ (∅ : Set α), ∀ c ∈ (∅ : Set α), f a b ∈ (∅ : Set α) ∧ f a b = f b a
    ∧ f (f a b) c = f a (f b c) ∧ f (g a b) c = g (f a c) (f b c)
    ∧ f a (g b c) = g (f a b) (f a c) := of_iff_true Set.forall_mem_empty

/-- Fact Of The Day 7: This statement is true. -/
theorem fotd7 : True := trivial

/-! TODO: FOTD 8 (define rubik's cube) -/

/-- Fact Of The Day 13: There can't be a bijection between any set and the set of bijections
between it and the empty set. -/
theorem fotd13 : IsEmpty (α ≃ (α ≃ Empty)) := by
  rw [isEmpty_iff]; intro e
  by_cases! h : IsEmpty α
  · exact h.false (e.symm (Equiv.equivEmpty α))
  · exact h.elim fun a => (e a a).elim

/-- Fact Of The Day 16: All primes are coprime. -/
theorem fotd16 (p q : Nat.Primes) (ne : p ≠ q) : Nat.Coprime p q :=
  (Nat.coprime_primes p.prop q.prop).mpr fun h => ne (Subtype.ext h)

/-- Fact Of The Day 17: Gain i dollars every day and in i days you will owe one dollar. -/
theorem fotd17 : Complex.I * Complex.I = -1 := Complex.I_mul_I

/-! TODO: FOTD 20 (hairy ball theorem) -/

/-- Fact Of The Day 26: There's the same amount of primes and composites. -/
theorem fotd26 : Cardinal.mk Nat.Primes = Cardinal.mk {n | ¬Nat.Prime n} := by
  trans Cardinal.aleph0
  · exact Cardinal.mk_eq_aleph0 _
  · symm; convert @Cardinal.mk_eq_aleph0 _ _ _
    · infer_instance
    apply Infinite.of_injective fun n => ⟨n ^ 2, Nat.Prime.not_prime_pow le_rfl⟩
    intro a b; simp

/-- Fact Of The Day 31: The pattern of prime numbers is that they all are prime. -/
theorem fotd31 (p : Nat.Primes) : Nat.Prime p := p.prop

/-! TODO: FOTD 36 (define chess positions) -/

/-- Fact Of The Day 38: 0 is the only complex number that doesn't have 2 complex square roots. -/
theorem fotd38 {c : ℂ} : (∃ r₁ r₂, r₁ ≠ r₂ ∧ r₁ ^ 2 = c ∧ r₂ ^ 2 = c) ↔ c ≠ 0 := by
  constructor
  · rintro ⟨r₁, r₂, hne, h1, h2⟩; contrapose hne; simp_all
  · intro hc
    use c.sqrt, -c.sqrt
    simpa [self_eq_neg, Complex.sqrt]

open MeasureTheory Measure in
/-- Fact Of The Day 39: A random number from 1 to 10 can have a 90% probability to be 5. It doesn't
stop it from being random. -/
theorem fotd39 : ∃ μ : Measure ℕ, IsProbabilityMeasure μ ∧ μ (Set.Icc 1 10) = 1 ∧
    μ {5} = 0.9 := by
  use (1 / 10 : ENNReal) • dirac 4 +  (9 / 10 : ENNReal) • dirac 5
  and_intros
  · constructor; norm_num [-one_div, ENNReal.div_add_div_same]
    apply ENNReal.div_self <;> norm_num
  · norm_num [-one_div, ENNReal.div_add_div_same]
    apply ENNReal.div_self <;> norm_num
  · simp [NNRatCast.ofScientific_eq_ite, NNRat.divNat_eq_div]
    unfold NNRat.cast NNRatCast.nnratCast ENNReal.instNNRatCast; simp

/-- Fact Of The Day 41: There are as many unique numbers as there are numbers. -/
theorem fotd41 : Cardinal.mk ℕ = Cardinal.mk ℕ := rfl

/-! TODO: FOTD 42 -/

/-- Fact Of The Day 43: `3-1 = (0, 1)`. -/
theorem fotd43 : (3 - 1 : Ordinal).toZFSet = {Ordinal.toZFSet 0, Ordinal.toZFSet 1} := by
  convert_to (1 + (0 + 1 + 1) - 1 : Ordinal).toZFSet = {∅, Ordinal.toZFSet (0 + 1)}
  · norm_num
  · norm_num
  simp [-zero_add]; ext; simp; exact or_comm

/-- Fact Of The Day 51: You can't fit `ω₁` onto the real number line. -/
theorem fotd51 : IsEmpty (Set.Iio (Ordinal.omega.{u} 1) ↪o ℝ) := by
  constructor; intro f
  suffices Set.Iio (Ordinal.omega.{u} 1) ↪o ℚ by
    simpa using Cardinal.lift_mk_le'.mpr ⟨this.toEmbedding⟩
  have : NoMaxOrder (Set.Iio (Ordinal.omega.{u} 1)) :=
    (Cardinal.isSuccLimit_omega 1).isSuccPrelimit.noMaxOrder_Iio
  have : ∀ o : Set.Iio (Ordinal.omega.{u} 1), ∃ q : ℚ, f o < q ∧ q < f (Order.succ o) :=
    fun o => exists_rat_btwn (f.strictMono (Order.lt_succ o))
  choose g h h' using this; apply OrderEmbedding.ofStrictMono g
  intro o1 o2 ho
  grw [← Rat.cast_lt (K := ℝ), h', ← h, f.le_iff_le, Order.succ_le_iff]; assumption

/-- Fact Of The Day 54: "Strawberry" has some letters in it. -/
theorem fotd54 : ∃ c : Char, "strawberry".contains c := ⟨'s', by simp⟩

/-- Fact Of The Day 60: "Snow is white" if, and only if, snow is white. -/
theorem fotd60 {snow : α} {IsWhite : α → Prop} : IsWhite snow ↔ IsWhite snow := Iff.rfl

/-- Fact Of The Day 67: Christmas never falls on friday the 13th. -/
theorem fotd67 {date : Std.Time.PlainDate} (isXmas : (date.day, date.month) = (25, .december)) :
    (date.weekday, date.day) ≠ (.friday, 13) := by simp_all; intro; decide

/-- Fact Of The Day 72: If you have 10 balls, and destroy at most 8, you still have 10 balls, just
change your base to how many balls there are. -/
theorem fotd72 (h : n ≤ 8) : ∃ b, String.ofList ((10 - n).toDigits b) = "10" := by
  use 10 - n
  rw [Nat.toDigits_of_base_le (by omega) le_rfl, Nat.div_self (by omega),
    Nat.toDigits_of_lt_base (by omega)]; simp; rfl

/-! TODO: FOTD 84 -/

/-
@[simp]
theorem Std.Time.PlainDate.toEpochDay_ofEpochDay {day : Day.Offset} :
    (ofEpochDay day).toEpochDay = day := by sorry

open Std.Time in
/-- Fact Of The Day 87: The midnight that starts the upcoming Friday will never be any more than
168 hours away, as long as you do not switch timezones while you are waiting. -/
theorem fotd87 {now : PlainDateTime} :
    ((now.date + (1 : Day.Offset)).withWeekday .friday).atTime .midnight - now
    ≤ (168 : Hour.Offset) := by
  rcases now with ⟨date, time⟩; dsimp
  have h1 : ((date + (1 : Day.Offset)).withWeekday .friday).toEpochDay ≤ date.toEpochDay + 7 := by
    change ((date.addDays 1).withWeekday _).toEpochDay ≤ _
    unfold PlainDate.withWeekday PlainDate.addDays; simp
    change _ + 1 + Internal.Bounded.LE.toInt _ ≤ _ + (1 + 6)
    rw [Int.add_assoc]; gcongr
    exact (_ : Internal.Bounded.LE _ _).2.2
  change PlainDateTime.toWallTime _ - PlainDateTime.toWallTime _ ≤ (168 : Hour.Offset)
  unfold PlainDate.atTime PlainDateTime.toWallTime; simp
  conv => lhs; lhs; arg 1; arg 1; change (_ + 0) * 1000000000 + 0
  simp [Internal.UnitVal.mul]
  change (Duration.ofNanoseconds _).sub (Duration.ofNanoseconds _) ≤ _
-/

/-! TODO: FOTD 87 (time library verification) -/

/-- Fact Of The Day 94: You can use a sphere as a dice with Aleph 1 possible results. Or Aleph 2.
Or Aleph 3. Nobody knows. -/
theorem fotd94 {c : EuclideanSpace ℝ (Fin 3)} {r : ℝ} (h : 0 < r) :
    ∃ o > (0 : Ordinal), Cardinal.mk (Metric.sphere c r) = Cardinal.aleph o := by
  suffices Uncountable (Metric.sphere c r) by
    have := Cardinal.mem_range_aleph_iff.mpr (Cardinal.aleph0_le_mk (Metric.sphere c r))
    simp [-Cardinal.range_aleph] at this; rcases this with ⟨o, h⟩
    refine ⟨o, ?_, h.symm⟩
    simp [zero_lt_iff]; intro rfl; simp at h
    exact ne_of_lt (Cardinal.aleph0_lt_mk) h
  suffices Uncountable (Set.Ico 0 (2 * Real.pi)) by
    apply Function.Injective.uncountable (α := Set.Ico 0 (2 * Real.pi)); swap
    · intro θ
      use c + .toLp _ (Fin.cons 0 ((finTwoArrowEquiv ℝ).symm (Complex.equivRealProd (circleMap 0 r θ))))
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_three, sq, ← Complex.normSq_apply,
        ← Complex.norm_def]; exact h.le
    · intro θ₁ θ₂; simp
      intro h₁ h₂; have := Complex.ext h₁ h₂
      ext; exact injOn_circleMap_of_abs_sub_le' h.ne' (sub_zero _).le θ₁.prop θ₂.prop this
  exact Cardinal.aleph0_lt_mk_iff.mp
    (by simpa [Cardinal.mk_Ico_real, Real.pi_pos] using Cardinal.aleph0_lt_continuum)

/-- Fact Of The Day 100: 100 is the square root of a whole number. -/
theorem fotd100 : ∃ n, 100 * 100 = n := ⟨_, rfl⟩

/-- Fact Of The Day 101: !false = false! -/
theorem fotd101 : (!false).toNat = Nat.factorial false.toNat := rfl

/-- Fact Of The Day 102: prime1(prime3)+prime4=prime7

(`Nat.nth` is 0-indexed) -/
theorem fotd102 :
    Nat.nth Nat.Prime 0 * Nat.nth Nat.Prime 2 + Nat.nth Nat.Prime 3 = Nat.nth Nat.Prime 6 := by
  simp; symm; exact Nat.nth_count (show Nat.Prime 17 by decide)

/-- Fact Of The Day 126: 1 -/
theorem fotd126 : Bool.ofNat 1 := rfl

/-- Fact Of The Day 174: {false} -/
theorem fotd174 : {Ordinal.toZFSet false.toNat} = Ordinal.toZFSet true.toNat := by
  simp; rw [← zero_add (1 : Ordinal), Ordinal.toZFSet_add_one]; simp

/-- Fact Of The Day 178:
$$
  \int_{false}^{true}truedx
$$ -/
theorem fotd178 : ∫ _ in false.toNat..true.toNat, (true.toNat : ℝ) = true.toNat := by simp

/-- Fact Of The Day 179: cos(false) -/
theorem fotd179 : Real.cos false.toNat = true.toNat := by simp

/-- Fact Of The Day 183: Euler's number, denoted as e, is greater than -48367193 -/
theorem fotd183 : -48367193 < Real.exp 0 := by trans 0 <;> simp

/-- Fact Of The Day 188: The word "palindrome" is heterological. -/
theorem fotd188 : ¬"palindrome".toList.Palindrome := by decide

/-! TODO: FOTD 196 (i do not like it) -/

/-- Fact Of The Day 198: Any two different points are parallel. -/
theorem fotd198 [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P] {p₁ p₂ : P} :
    (affineSpan k {p₁}).Parallel (affineSpan k {p₂}) := by
  simp [AffineSubspace.affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty]

/-- Fact Of The Day 199: The length measure of the set of rational numbers is rational. -/
theorem fotd199 : (MeasureTheory.volume (Set.range ((↑) : ℚ → ℝ))).toEReal ∈
    Set.range fun q : ℚ => ((q : Real) : EReal) := by
  use 0; symm; simp
  apply (Set.countable_range Rat.cast).measure_zero

/-- Fact Of The Day 202: If there's an infinite amount of integers, one of them must be called
twenty five. -/
theorem fotd202 : Infinite ℤ → ∃ z, z = 25 := by simp

/-! TODO: FOTD 214 (area of a sphere/cube) -/
