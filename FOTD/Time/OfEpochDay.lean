import Mathlib.Algebra.Order.Ring.Int

@[simp]
theorem Int.dvd_sub_left {a b c : ℤ} (H : a ∣ c) : a ∣ b - c ↔ a ∣ b where
  mp h := by simpa using Int.dvd_add H h
  mpr h := Int.dvd_sub h H

theorem Int.ite_tdiv_add_one {a b : ℤ} (h : 0 ≤ b) :
    (if a ≥ 0 then a else a - b).tdiv (b + 1) = a / (b + 1) := by
  split; · apply tdiv_eq_ediv_of_nonneg; assumption
  rename_i ha; rw [← sub_add_cancel (a - b) 1, sub_sub, add_one_tdiv, tdiv_eq_ediv,
    sign_eq_one_of_pos (by omega), add_assoc, sub_ediv_of_dvd _ dvd_rfl, Int.ediv_self (by omega)]
  omega

theorem Int.ediv_le_ediv_right {a b c : ℤ} (ha : 0 ≤ a) (hb : 0 < b) (hc : b ≤ c) : a / c ≤ a / b := by
  rw [le_iff_eq_or_lt] at ha; rcases ha with (rfl | ha); · simp
  rw [← Int.mul_ediv_mul_of_pos a c hb, mul_comm, ← Int.mul_ediv_mul_of_pos_left a b (hb.trans_le hc)]
  apply Int.ediv_le_ediv (mul_pos hb (hb.trans_le hc)); apply mul_le_mul <;> omega

instance Int.decidableForallLeLt [DecidablePred P] {lo hi : ℤ} :
    Decidable (∀ z, lo ≤ z → z < hi → P z) :=
  decidable_of_iff (∀ n < (hi - lo).toNat, P (lo + n)) (by
    simp; constructor
    · intro H z hl hh; simpa [hl] using H (z - lo).toNat (by simpa [hh] using hl.trans_lt hh)
    · intro H n h; exact H _ (by simp) (by omega)
  )

namespace Std.Time.Internal.Bounded.LE

@[simp]
theorem val_eq_toInt {lo hi} {b : Bounded.LE lo hi} : b.val = b.toInt := rfl

@[simp]
theorem toInt_clip {lo hi val : ℤ} (h₀ : lo ≤ val) (h₁ : val ≤ hi) :
    (clip val (h₀.trans h₁)).toInt = val := by
  rw (transparency := .default) [clip, dite_eq_left h₀, dite_eq_left h₁]; rfl

end Internal.Bounded.LE

namespace PlainDate.ofEpochDay
def z (day : Day.Offset) := day.val + 719468
def era (day) := (if z day ≥ 0 then z day else z day - 146096).tdiv 146097
def doe (day) := z day - era day * 146097
def yoe (day) := (doe day - (doe day).tdiv 1460 + (doe day).tdiv 36524 - (doe day).tdiv 146096).tdiv 365
def y (day) := yoe day + era day * 400
def doy (day) := doe day - (365 * yoe day + (yoe day).tdiv 4 - (yoe day).tdiv 100)
def mp (day) := (5 * doy day + 2).tdiv 153
def d (day) := doy day - (153 * mp day + 2).tdiv 5 + 1
def m (day) := mp day + (if mp day < 10 then 3 else -9)

theorem era_eq_div {day} : era day = z day / 146097 := Int.ite_tdiv_add_one (by decide)
theorem doe_eq_mod {day} : doe day = z day % 146097 := by
  rw [doe, era_eq_div, mul_comm, Int.emod_def]
theorem doe_nonneg {day} : 0 ≤ doe day := by rw [doe_eq_mod]; apply Int.emod_nonneg; decide
theorem doe_lt {day} : doe day < 146097 := by rw [doe_eq_mod]; apply Int.emod_lt; decide
theorem yoe_eq_div {day} :
    yoe day = (doe day - (doe day) / 1460 + (doe day) / 36524 - (doe day) / 146096) / 365 := by
  unfold yoe; repeat rw [Int.tdiv_eq_ediv_of_nonneg doe_nonneg]
  rw [Int.tdiv_eq_ediv_of_nonneg]; rw [add_sub_assoc]; apply add_nonneg <;> simp
  · apply Int.ediv_le_self _ doe_nonneg
  · apply Int.ediv_le_ediv_right doe_nonneg <;> decide
theorem yoe_nonneg {day} : 0 ≤ yoe day := by
  rw [yoe_eq_div]; apply Int.ediv_nonneg _ (by decide); rw [add_sub_assoc]; apply add_nonneg <;> simp
  · apply Int.ediv_le_self _ doe_nonneg
  · apply Int.ediv_le_ediv_right doe_nonneg <;> decide
theorem yoe_lt {day} : yoe day < 400 := by
  rw [yoe_eq_div]; by_cases! h : doe day ≤ 145999
  · grw [← add_sub_right_comm, Int.ediv_le_ediv (by decide)]
    case H' => grw [Int.ediv_le_ediv_right doe_nonneg (by decide : (0 : ℤ) < 1460) (by decide),
      add_sub_cancel_right, ← Int.ediv_nonneg (doe_nonneg) (by decide), sub_zero, h]
    decide
  · have h' := @doe_lt day
    revert h' h; generalize doe day = d
    rw [Int.lt_iff_add_one_le]; revert d; decide -- 97 cases
theorem doy_eq {day} : doy day = doe day - 365 * yoe day - (yoe day) / 4 + (yoe day) / 100 := by
  simp [doy, sub_sub, sub_add, Int.tdiv_eq_ediv_of_nonneg yoe_nonneg]
theorem doy_nonneg {day} : 0 ≤ doy day := by
  rw [doy_eq, yoe_eq_div]
  have := @doe_lt day; revert this
  have := @doe_nonneg day; revert this
  generalize doe day = d; revert d; native_decide -- fuck it
theorem doy_lt {day} : doy day < 366 := by
  rw [doy_eq, yoe_eq_div]
  have := @doe_lt day; revert this
  have := @doe_nonneg day; revert this
  generalize doe day = d; revert d; native_decide
theorem mp_eq_div {day} : mp day = (5 * doy day + 2) / 153 := by
  rw [mp, Int.tdiv_eq_ediv_of_nonneg]; grw [← doy_nonneg] <;> decide
theorem mp_nonneg {day} : 0 ≤ mp day := by
  apply Int.tdiv_nonneg _ (by decide); grw [← doy_nonneg] <;> decide
theorem mp_lt {day} : mp day < 12 := by
  grw [mp_eq_div, Int.ediv_le_ediv (by decide) (by grw [doy_lt]; decide)]; decide
theorem d_eq {day} : d day = doy day - (153 * mp day + 2) / 5 + 1 := by
  rw [d, Int.tdiv_eq_ediv_of_nonneg]; grw [← mp_nonneg] <;> decide
theorem le_d {day} : 1 ≤ d day := by
  rw [d_eq, mp_eq_div, doy_eq, yoe_eq_div]
  have := @doe_lt day; revert this
  have := @doe_nonneg day; revert this
  generalize doe day = d; revert d; native_decide
theorem d_le {day} : d day ≤ 31 := by
  rw [d_eq, mp_eq_div, doy_eq, yoe_eq_div]
  have := @doe_lt day; revert this
  have := @doe_nonneg day; revert this
  generalize doe day = d; revert d; native_decide

end ofEpochDay

section open ofEpochDay

theorem ofEpochDay_eq_clip {day} :
    ofEpochDay day = ofYearMonthDayClip (y day + (if m day <= 2 then 1 else 0 : ℤ))
      (.clip (m day) (by decide)) (.clip (d day) (by decide)) := rfl

theorem year_ofEpochDay {day} :
    (ofEpochDay day).year.toInt = y day + (if m day <= 2 then 1 else 0 : ℤ) :=
  congrArg year ofEpochDay_eq_clip

theorem month_ofEpochDay {day} : (ofEpochDay day).month.toInt = m day := by
  rw [ofEpochDay_eq_clip, m]; apply Internal.Bounded.LE.toInt_clip
  · have := @mp_nonneg day; omega
  · have := @mp_lt day; omega

theorem day_ofEpochDay {day} : (ofEpochDay day).day.toInt = d day := by
  rw [ofEpochDay_eq_clip]; unfold ofYearMonthDayClip Month.Ordinal.clipDay; simp
  rw (transparency := .default) [Internal.Bounded.LE.toInt_clip le_d d_le, ite_eq_right,
    Internal.Bounded.LE.toInt_clip le_d d_le]
  rw [y, Year.Offset.isLeap, Bool.decide_congr (by rw [ne_eq, ← Int.dvd_iff_tmod_eq_zero,
    ← Int.dvd_iff_tmod_eq_zero, ← Int.dvd_iff_tmod_eq_zero, Year.Offset.toInt, add_right_comm,
    Int.dvd_add_left, Int.dvd_add_left (b := _ + _), Int.dvd_add_left (b := _ + _)] <;> omega)]
  rw [m, d_eq, mp_eq_div, doy_eq, yoe_eq_div]
  have := @doe_lt day; revert this
  have := @doe_nonneg day; revert this
  generalize doe day = d; revert d; native_decide

end

namespace toEpochDay
def y (date : PlainDate) := if date.month.toInt > 2 then date.year.toInt else date.year.toInt - 1
def era (date) := (if y date ≥ 0 then y date else y date - 399).tdiv 400
def yoe (date) := y date - era date * 400
def mp (date : PlainDate) := date.month.toInt + (if date.month.toInt > 2 then -3 else 9)
def doy (date) := (153 * (mp date) + 2).tdiv 5 + date.day.toInt - 1
def doe (date) := yoe date * 365 + (yoe date).tdiv 4 - (yoe date).tdiv 100 + doy date

theorem y_ofEpochDay {day} : y (ofEpochDay day) = ofEpochDay.y day := by
  rw [y, month_ofEpochDay, year_ofEpochDay]; omega
theorem era_ofEpochDay {day} : era (ofEpochDay day) = ofEpochDay.era day := by
  rw [era, show (400 : ℤ) = 399 + 1 from rfl, Int.ite_tdiv_add_one (by decide)]; simp
  rw [y_ofEpochDay, ofEpochDay.y, Int.add_mul_ediv_right _ _ (by decide),
    Int.ediv_eq_zero_of_lt ofEpochDay.yoe_nonneg ofEpochDay.yoe_lt, zero_add]
theorem yoe_ofEpochDay {day} : yoe (ofEpochDay day) = ofEpochDay.yoe day := by
  rw [yoe, y_ofEpochDay, era_ofEpochDay, ofEpochDay.y, add_sub_cancel_right]
theorem mp_ofEpochDay {day} : mp (ofEpochDay day) = ofEpochDay.mp day := by
  rw [mp, month_ofEpochDay, ofEpochDay.m]
  have := @ofEpochDay.mp_nonneg day; have := @ofEpochDay.mp_lt day; omega
theorem doy_ofEpochDay {day} : doy (ofEpochDay day) = ofEpochDay.doy day := by
  rw [doy, mp_ofEpochDay, day_ofEpochDay, ofEpochDay.d, add_sub_assoc]; simp
theorem doe_ofEpochDay {day} : doe (ofEpochDay day) = ofEpochDay.doe day := by
  rw [doe, yoe_ofEpochDay, doy_ofEpochDay, ofEpochDay.doy]; omega

end toEpochDay

section open toEpochDay

theorem val_toEpochDay {date} :
    (toEpochDay date).val = toEpochDay.era date * 146097 + doe date - 719468 := rfl

@[simp]
theorem toEpochDay_ofEpochDay {day : Day.Offset} :
    (ofEpochDay day).toEpochDay = day := by
  apply Internal.UnitVal.ext; rw [val_toEpochDay, era_ofEpochDay, doe_ofEpochDay,
    ofEpochDay.era_eq_div, ofEpochDay.doe_eq_mod, Int.ediv_mul_add_emod, ofEpochDay.z,
    add_sub_cancel_right]

end
