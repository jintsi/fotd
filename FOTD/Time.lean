import FOTD.Time.OfEpochDay

theorem Int.mul_add_tdiv_eq_right {a b c : ℤ}
    (h : 0 ≤ b ∧ 0 ≤ c ∧ c < a ∨ b ≤ 0 ∧ c ≤ 0 ∧ -a < c) : (a * b + c).tdiv a = b := by
  have ha : 0 < a := h.elim (fun h => h.2.1.trans_lt h.2.2)
    (fun h => pos_of_neg_neg (h.2.2.trans_le h.2.1))
  rw [tdiv_eq_ediv, sign_eq_one_of_pos ha, mul_add_ediv_left b c ha.ne']; simp
  by_cases! hc : 0 ≤ c
  · rw [ite_eq_left, add_zero, add_eq_left]
    · exact ediv_eq_zero_of_lt hc (h.elim (fun h => h.2.2) fun h => h.2.1.trans_lt ha)
    · rcases h with (h | h)
      · left; exact add_nonneg (mul_nonneg ha.le h.1) hc
      · right; rw [le_antisymm h.2.1 hc]; exact a.dvd_zero
  · rw [or_iff_right fun h => hc.not_ge h.2.1] at h
    rw [ite_eq_right, add_assoc, add_eq_left, add_eq_zero_iff_eq_neg]
    · exact ediv_eq_neg_one_of_neg_of_le hc (neg_le_of_neg_le h.2.2.le)
    · simp; and_intros
      · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha.le h.1) hc
      · rw [not_dvd_iff_lt_mul_succ c ha]; use -1; simp; exact ⟨h.2.2, hc⟩

namespace Std.Time.Internal.Bounded.LE

@[ext]
theorem ext {lo hi} {x y : Bounded.LE lo hi} (h : x.toInt = y.toInt) : x = y := Subtype.ext h

theorem le_toInt {lo hi} (b : Bounded.LE lo hi) : lo ≤ b.toInt := b.prop.1
theorem toInt_le {lo hi} (b : Bounded.LE lo hi) : b.toInt ≤ hi := b.prop.2

@[simp]
theorem toInt_neg {lo hi} {b : Bounded.LE lo hi} : b.neg.toInt = -b.toInt := rfl

@[simp]
theorem toInt_byMod {b i : ℤ} {hi : 0 < i} : (byMod b i hi).toInt = b.tmod i := rfl

end Bounded.LE

namespace UnitVal

@[simp]
theorem val_zero : (0 : UnitVal α).val = 0 := rfl

@[simp]
theorem val_ofNat {n : ℕ} : (ofNat(n) : UnitVal α).val = n := rfl

@[simp]
theorem val_add {u1 u2 : UnitVal α} : (u1 + u2).val = u1.val + u2.val := rfl

@[simp]
theorem val_neg {u : UnitVal α} : (-u).val = -u.val := rfl

@[simp]
theorem val_mul {u : UnitVal α} {f : ℤ} : (u.mul f).val = f * u.val := mul_comm _ _

@[simp]
theorem val_tdiv {u : UnitVal α} {d : ℤ} : (u.tdiv d).val = u.val.tdiv d := rfl

@[simp]
theorem val_cast {h : α = β} {u : UnitVal α} : (u.cast h).val = u.val := rfl

end Internal.UnitVal

set_option allowUnsafeReducibility true in
attribute [reducible] Nanosecond.Span

set_option allowUnsafeReducibility true in
attribute [reducible] Nanosecond.Ordinal

set_option allowUnsafeReducibility true in
attribute [reducible] Day.Offset Hour.Offset Minute.Offset Second.Offset Nanosecond.Offset

@[simp]
theorem Nanosecond.Offset.val_ofInt {d : ℤ} : (ofInt d).val = d := rfl

namespace Duration

instance instAdd : Add Duration := ⟨add⟩

instance instNeg : Neg Duration := ⟨Duration.neg⟩

instance instSub : Sub Duration := ⟨sub⟩

@[simp]
theorem add_eq {x y : Duration} : x.add y = x + y := rfl

@[simp]
theorem neg_eq {x : Duration} : x.neg = -x := rfl

@[simp]
theorem sub_eq {x y : Duration} : x.sub y = x - y := rfl

@[simp]
theorem toNanoseconds_ofNanoseconds {n : Nanosecond.Offset} :
    (ofNanoseconds n).toNanoseconds = n := by
  unfold ofNanoseconds toNanoseconds Nanosecond.Offset at *
  apply Internal.UnitVal.ext; simp [Int.mul_tdiv_add_tmod]

@[simp]
theorem ofNanoseconds_toNanoseconds {dur : Duration} : ofNanoseconds dur.toNanoseconds = dur := by
  have := by
    simpa using dur.proof.imp
      (And.imp_right fun h2 => And.intro h2 (Int.lt_add_one_of_le dur.nano.toInt_le))
      (And.imp_right fun h2 => And.intro h2 (Int.sub_one_lt_of_le dur.nano.le_toInt))
  unfold toNanoseconds ofNanoseconds; ext
  · simp; exact Int.mul_add_tdiv_eq_right this
  · simp; rw [Int.tmod_def, Int.mul_add_tdiv_eq_right this, add_sub_cancel_left]

@[ext 2000]
theorem extNano {x y : Duration} (h : x.toNanoseconds = y.toNanoseconds) : x = y := by
  simpa using congrArg ofNanoseconds h

@[simp]
theorem toNanoseconds_ofSeconds : (ofSeconds s).toNanoseconds = s.toNanoseconds := by
  ext; exact add_zero _

@[simp]
theorem toNanoseconds_zero : (0 : Duration).toNanoseconds = 0 := rfl

@[simp]
theorem toNanoseconds_add {x y : Duration} :
  (x + y).toNanoseconds = x.toNanoseconds + y.toNanoseconds := toNanoseconds_ofNanoseconds

@[simp]
theorem toNanoseconds_neg {x : Duration} : (-x).toNanoseconds = -x.toNanoseconds := by
  unfold toNanoseconds; ext; simp [← neg_eq, Duration.neg, -neg_add_rev, neg_add]
  change _ * -_ = _; simp

instance addCommGroup : AddCommGroup Duration where
  add := add
  add_assoc a b c := by ext; simp [add_assoc]
  zero_add a := by ext; simp
  add_zero a := by ext; simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by ext; simp
  add_comm a b := by ext; simp [add_comm]

theorem le_iff {x y : Duration} : x ≤ y ↔ x.toNanoseconds.val ≤ y.toNanoseconds.val := Iff.rfl

theorem lt_iff {x y : Duration} : x < y ↔ x.toNanoseconds.val < y.toNanoseconds.val := Iff.rfl

instance linearOrder : LinearOrder Duration where
  le_refl a := Int.le_refl _
  le_trans a b c := by simp [le_iff]; exact le_trans
  lt_iff_le_not_ge a b := by simp [lt_iff, le_iff]; exact le_of_lt
  le_antisymm a b h1 h2 := by ext; exact le_antisymm h1 h2
  compare x y := compareOfLessAndEq x y
  le_total a b := by simp [le_iff]; exact le_total
  toDecidableLE a b := instDecidableLe

instance isOrderedAddMonoid : IsOrderedAddMonoid Duration where
  add_le_add_left a b := by simp [le_iff]

end Duration

namespace WallTime

@[simp]
theorem val_ofSeconds : (ofSeconds s).val = Duration.ofSeconds s := rfl

@[simp]
theorem val_ofNanoseconds : (ofNanoseconds n).val = Duration.ofNanoseconds n := rfl

end WallTime

namespace PlainTime

@[simp]
theorem toWallTime_midnight : midnight.toWallTime.val = 0 := rfl

theorem toWallTime_nonneg {time : PlainTime} : 0 ≤ time.toWallTime.val := by
  unfold toWallTime; simp [Duration.le_iff]; unfold toNanoseconds
  repeat apply add_nonneg
  · simp [Hour.Offset.toNanoseconds, Hour.Ordinal.toOffset]; exact time.hour.prop.1
  · simp [Minute.Offset.toNanoseconds, Minute.Ordinal.toOffset]; exact time.minute.prop.1
  · simp [Second.Offset.toNanoseconds, Second.Ordinal.toOffset]; exact time.second.prop.1
  · simp [Nanosecond.Ordinal.toOffset]; exact time.nanosecond.prop.1

end PlainTime

namespace PlainDate

@[simp]
theorem toWallTime_addDays {date : PlainDate} {d : Day.Offset} :
    (date.addDays d).toWallTime.val = date.toWallTime.val + d := by
  ext; simp [toWallTime, addDays, Second.Offset.toNanoseconds, Day.Offset.toSeconds, mul_add]

@[simp]
theorem atTime_eq {date : PlainDate} {time : PlainTime} : date.atTime time = ⟨date, time⟩ := rfl

end PlainDate

namespace PlainDateTime

@[simp]
theorem toWallTime_mk {date : PlainDate} {time : PlainTime} :
    (mk date time).toWallTime.val = date.toWallTime.val + time.toWallTime.val := by
  unfold toWallTime PlainDate.toWallTime PlainTime.toWallTime; ext
  simp [mul_add, Second.Offset.toNanoseconds, add_assoc]
  unfold PlainTime.toNanoseconds PlainTime.toSeconds
  change _ * (_ + _ + _) + _ = _ + _ + _ + time.nanosecond.val
  simp [mul_add, Hour.Offset.toSeconds, Minute.Offset.toSeconds, Hour.Offset.toNanoseconds,
    Minute.Offset.toNanoseconds, Second.Offset.toNanoseconds, ← mul_assoc]

@[simp]
theorem sub_eq {x y : PlainDateTime} : x - y = x.toWallTime.val - y.toWallTime.val := rfl
