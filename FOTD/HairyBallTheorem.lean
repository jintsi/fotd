import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! Taken straight from https://github.com/corent1234/hairy-ball-theorem-lean -/

set_option autoImplicit false

open scoped RealInnerProductSpace
open scoped BigOperators

variable (n : ℕ) (n_pos : 0 < n) (hn : 1 < n) (odd_n : Odd n)

local notation3 "E" n:1023 => EuclideanSpace ℝ (Fin n)
abbrev unitSphere := Metric.sphere (0 : E n) 1

structure IsExtensionOfVectorFieldOnSn (v : E n → E n) where
  isCont : Continuous v
  isTang : ∀ x : E n, ⟪x, (v x)⟫ = 0
  isExtension : ∀ x : E n, ∀ r : ℝ, r ≥ 0 → v (r • x) = r • v x



section Lipschitz_section

lemma ContDiffOn.locallyLipschitzOn_of_isOpen {𝕂 : Type} [RCLike 𝕂] {E' : Type} [NormedAddCommGroup E']
    [NormedSpace 𝕂 E'] {F' : Type} [NormedAddCommGroup F'] [NormedSpace 𝕂 F'] {f : E' → F'}
    {s : Set E'} (hf : ContDiffOn 𝕂 1 f s) (hs : IsOpen s) :
    LocallyLipschitzOn s f := by
  intro x hx
  obtain ⟨K, t', ht', hK⟩ := (hf.contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨K, t', mem_nhdsWithin_of_mem_nhds ht', hK⟩

lemma ENNReal.ofReal_ne_zero {p : ℝ} : ENNReal.ofReal p ≠ 0 ↔ 0 < p := by
  rw [← not_le, not_iff_not, ENNReal.ofReal_eq_zero]

lemma LocallyLipschitzOn.lipshitzOnWith_of_isCompact {𝕂 : Type} [RCLike 𝕂] {E' : Type}
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] {F' : Type} [NormedAddCommGroup F']
    [NormedSpace 𝕂 F'] {f : E' → F'} {s t : Set E'} (hf : LocallyLipschitzOn t f)
    (hs : IsCompact s) (ht : t ∈ nhdsSet s) :
    ∃ K, LipschitzOnWith K f s := by
  have f_continuousOn : ContinuousOn f s :=
    hf.continuousOn.mono (subset_of_mem_nhdsSet ht)
  choose K s' hK using hf
  obtain ⟨t', ht'⟩ := hs.elim_nhds_subcover' (fun x hx => interior (s' (subset_of_mem_nhdsSet ht hx)))
    (fun x hx => interior_mem_nhds.2 (nhds_of_nhdsWithin_of_nhds (nhds_le_nhdsSet hx ht)
    (hK (subset_of_mem_nhdsSet ht hx)).1))
  by_cases t'_empty : t' = ∅
  · simp only [t'_empty, Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty,
      Set.subset_empty_iff] at ht'
    rw [ht']
    exact ⟨0, lipschitzOnWith_empty _ _⟩
  have ht'' : s ⊆ Set.iUnion (fun (x : t') => interior (s' (subset_of_mem_nhdsSet ht x.1.2))) := by
    rwa [Set.iUnion_subtype]
  let ⟨ε', hε', hε's⟩ := lebesgue_number_lemma_of_metric hs
    (fun (x : t') => isOpen_interior) ht''
  let K' : ℝ := (t'.image (fun x => K (Set.mem_of_subset_of_mem (subset_of_mem_nhdsSet ht) x.2))).max'
    ((Finset.nonempty_iff_ne_empty.2 t'_empty).image _)
  let K'' := (Metric.diam (f '' s)) / ε'
  by_cases hK'' : K'' = 0
  · have : Metric.diam (f '' s) = 0 := by
      rwa [← zero_mul ε', ← div_eq_iff hε'.ne']
    refine ⟨0, fun x hx y hy => ?_⟩
    rw [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero, edist_eq_zero, ← dist_le_zero,
      ← zero_mul ε', ← hK'', div_mul_cancel₀ _ hε'.ne']
    exact Metric.dist_le_diam_of_mem (hs.image_of_continuousOn f_continuousOn).isBounded
      (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy)
  have K''_pos : 0 < K'' := lt_of_le_of_ne (div_nonneg Metric.diam_nonneg hε'.le) (fun h => hK'' h.symm)
  have max_pos : 0 < max K' K'' := lt_max_of_lt_right K''_pos
  refine ⟨NNReal.mk (max K' K'') (le_max_of_le_left (NNReal.coe_nonneg _)), fun x hx y hy => ?_⟩
  by_cases hxy : edist x y < ENNReal.ofReal ε'
  · by_cases hxy' : x = y
    · simp [hxy']
    obtain ⟨i, hi⟩ := hε's x hx
    have hit : i.1.1 ∈ t := subset_of_mem_nhdsSet ht i.1.2
    have K_le_max : K hit ≤ max K' K'' := by
      refine le_trans (Finset.le_max' _ (K hit) (Finset.mem_image.2 ?_)) (le_max_left _ _)
      exact ⟨i, i.2, rfl⟩
    refine le_trans ?_ ((ENNReal.mul_le_mul_iff_left (edist_pos.2 hxy').ne'
      (lt_of_lt_of_le hxy le_top).ne).2 (ENNReal.coe_le_coe.2 K_le_max))
    exact (hK hit).2 (interior_subset (hi (Metric.mem_ball_self hε')))
      (interior_subset (hi (Metric.mem_ball'.2 (edist_lt_ofReal.1 hxy))))
  · have x_ne_y : x ≠ y :=
      edist_pos.1 (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hε') (not_lt.1 hxy))
    by_cases hxy' : edist x y = ⊤
    · rw [hxy', ENNReal.mul_top (by rwa [← ENNReal.ofReal_coe_nnreal, NNReal.coe_mk, ENNReal.ofReal_ne_zero])]
      exact le_top
    refine le_trans ?_ ((ENNReal.mul_le_mul_iff_left (edist_pos.2 x_ne_y).ne' hxy').2
      (ENNReal.ofReal_le_of_le_toReal (le_max_right K' K'')))
    refine le_trans ?_ ((ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_ne_zero.2 K''_pos)
      ENNReal.ofReal_ne_top).2 (not_lt.1 hxy))
    rw [← ENNReal.ofReal_mul K''_pos.le, div_mul_cancel₀ _ hε'.ne', edist_dist]
    exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem
      (hs.image_of_continuousOn f_continuousOn).isBounded
      (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy))

lemma LocallyLipschitz.lipshitzWith_of_CompactSpace {𝕂 : Type} [RCLike 𝕂] {E' : Type}
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] [CompactSpace E'] {F' : Type}
    [NormedAddCommGroup F'] [NormedSpace 𝕂 F'] {f : E' → F'} (hf : LocallyLipschitz f) :
    ∃ K, LipschitzWith K f := by
  obtain ⟨K, hK⟩ := hf.locallyLipschitzOn.lipshitzOnWith_of_isCompact (𝕂 := 𝕂)
    isCompact_univ Filter.univ_mem
  exact ⟨K, lipschitzOnWith_univ.1 hK⟩

lemma ContDiffOn.lipschitzOnWith_of_isCompact {𝕂 : Type} [RCLike 𝕂] {E' : Type}
    [NormedAddCommGroup E'] [NormedSpace 𝕂 E'] {F' : Type} [NormedAddCommGroup F']
    [NormedSpace 𝕂 F'] {f : E' → F'} {s t : Set E'} (hf : ContDiffOn 𝕂 1 f s)
    (ht : IsCompact t) (hs : s ∈ nhdsSet t) :
    ∃ K, LipschitzOnWith K f t :=
  ((hf.mono interior_subset).locallyLipschitzOn_of_isOpen (isOpen_interior)).lipshitzOnWith_of_isCompact
    (𝕂 := 𝕂) ht (isOpen_interior.mem_nhdsSet.2 (subset_interior_iff_mem_nhdsSet.2 hs))

end Lipschitz_section

section

variable (v : E n → E n) (hv : IsExtensionOfVectorFieldOnSn n v)
  (vUnit : ∀ x : E n, ‖v x‖ = ‖x‖)
  {A : Set (E n)} (AComp : IsCompact A)
  {s : Set (E n)} (hs : s ∈ nhdsSet A) (s_isOpen : IsOpen s)
  (vContDiff : ContDiffOn ℝ 1 v s)

local notation "f" => fun (t : ℝ) (x : E n) ↦ x + t • (v x)

local notation "crown" => fun (a b : ℝ) =>
  (Metric.ball (0 : E n) b) \ (Metric.closedBall 0 a)

local notation "closedCrown" => fun (a b : ℝ) =>
  (Metric.closedBall (0 : E n) b) \ (Metric.ball 0 a)

section crown_section

open Metric Set

variable {n}

lemma Metric.mem_crown {a b : ℝ} {x : E n} : x ∈ crown a b ↔ a < ‖x‖ ∧ ‖x‖ < b := by
  rw [mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le, and_comm]

lemma Metric.isOpen_crown (a b : ℝ) : IsOpen (crown a b) :=
  isOpen_ball.sdiff isClosed_closedBall

lemma isCompact_closedCrown (a b : ℝ) : IsCompact (closedCrown a b) :=
  (ProperSpace.isCompact_closedBall _ _).diff isOpen_ball

lemma Metric.crown_subset_closedCrown {a b : ℝ} : crown a b ⊆ closedCrown a b :=
  fun _ ⟨hxb, hxa⟩ => ⟨ball_subset_closedBall hxb,
    (compl_subset_compl.2 ball_subset_closedBall) hxa⟩

lemma measurableSet_closedCrown {a b : ℝ} : MeasurableSet (closedCrown a b) :=
  measurableSet_closedBall.diff measurableSet_ball

end crown_section


open Topology

variable {n} {v} (hs_crown : s ∈ nhdsSet ((Metric.closedBall (0 : E n) 2) \ (Metric.ball 0 2⁻¹)))

include hv in
lemma HairyBallTheorem.continuous_ft (t : ℝ) : Continuous (f t) :=
  continuous_id.add (continuous_const.fun_smul hv.isCont)

include hv in
lemma HairyBallTheorem.measurable_ft (t : ℝ) : Measurable (f t) :=
  measurable_id.add (measurable_const.fun_smul hv.isCont.measurable)

lemma eq_zero_of_le_self_of_lt_one {α : ℝ} (hα : 0 ≤ α) (t : ℝ) (ht : |t| < 1) (h : α ≤ |t| * α) :
    α = 0 := by
  by_contra!
  have : 1 ≤ |t| := by
    rwa [← mul_le_mul_iff_left₀ (hα.lt_of_ne (ne_comm.1 this)), one_mul]
  linarith

include AComp hs vContDiff in
/-- f t is injective on A for sufficiently small t. -/
lemma HairyBallTheorem.injOn_A_ft : ∀ᶠ t in 𝓝 0, A.InjOn (f t) := by
  let ⟨K, hK⟩ := vContDiff.lipschitzOnWith_of_isCompact AComp hs
  wlog K0 : K > 0
  · exact this AComp hs vContDiff _
      (LipschitzOnWith.weaken hK (le_add_of_nonneg_right zero_le_one))
      (add_pos_of_nonneg_of_pos zero_le one_pos)
  refine Metric.eventually_nhds_iff_ball.2 ⟨K⁻¹, ⟨inv_pos.2 K0, fun t ht x hx y hy h =>
    eq_of_sub_eq_zero (norm_eq_zero.1 (eq_zero_of_le_self_of_lt_one (norm_nonneg _)
    (t * K) ?_ ?_))⟩⟩
  · rw [abs_mul, abs_eq_self.2 K.coe_nonneg, ← Real.norm_eq_abs,
      ← inv_mul_cancel₀ (NNReal.coe_ne_zero.2 K0.ne')]
    exact (mul_lt_mul_iff_left₀ (NNReal.coe_pos.2 K0)).2 (mem_ball_zero_iff.1 ht)
  · have : x - y = t • (v y - v x) := by
      rw [smul_sub, sub_eq_sub_iff_add_eq_add, add_comm _ y]
      exact h
    nth_rw 1 [this]
    rw [abs_mul, abs_eq_self.2 K.coe_nonneg, mul_assoc, norm_smul, Real.norm_eq_abs,
      ← dist_eq_norm_sub, ← dist_eq_norm_sub, PseudoMetricSpace.dist_comm]
    by_cases t0 : t = 0
    · simp [t0]
    exact (mul_le_mul_iff_right₀ (abs_pos.2 t0)).2 (hK.dist_le_mul x hx y hy)

/-- derivative of f t at x -/
local notation "f'" t:max x:max =>
  (ContinuousLinearMap.id ℝ (E n)) + ((t : ℝ) • (fderiv ℝ v x))

include vContDiff hs in
/-- f' t x is the derivative of f t at x ∈ A -/
lemma HairyBallTheorem.ftDeriv (t : ℝ) : ∀ x ∈ A, HasFDerivWithinAt (f t) (f' t x) A x :=
  fun x hx => ((hasFDerivAt_id x).add
    (((vContDiff.differentiableOn one_ne_zero).differentiableAt
    (nhds_le_nhdsSet hx hs)).hasFDerivAt.const_smul t)).hasFDerivWithinAt

include vContDiff hs in
/-- f' t x is the (strict) derivative of f t at x ∈ A -/
lemma HairyBallTheorem.ftStrictDeriv (t : ℝ) : ∀ x ∈ A, HasStrictFDerivAt (f t) (f' t x) x :=
  fun x hx => (hasStrictFDerivAt_id x).add
    (((vContDiff.contDiffAt (nhds_le_nhdsSet hx hs)).hasStrictFDerivAt one_ne_zero).const_smul t)


section vol_poly

local notation "jac_f" =>
  fun (x : E n) ↦ LinearMap.toMatrix (PiLp.basisFun _ _ _) (PiLp.basisFun _ _ _) (fderiv ℝ v x : E n →ₗ[ℝ] E n)

open MeasureTheory

include AComp vContDiff hs in
lemma HairyBallTheorem.lintegral_abs_det_f't : ∀ᶠ t in 𝓝 0,
    ∫⁻ x in A, ENNReal.ofReal |(f' t x).det| ∂volume = volume ((f t) '' A) := by
  filter_upwards [injOn_A_ft AComp hs vContDiff] with t hinj
  exact lintegral_abs_det_fderiv_eq_addHaar_image volume
    AComp.measurableSet (ftDeriv hs vContDiff t) hinj

open Polynomial
open Finset
open Matrix

lemma Polynomial.natDegree_det (M : Matrix (Fin n) (Fin n) ℝ[X]) (h : ∀ i j, (M i j).natDegree ≤ 1) :
    M.det.natDegree ≤ n := by
  rw [det_apply]
  refine le_trans (natDegree_sum_le _ _) ((fold_max_le n).2 ⟨zero_le, fun σ _ => ?_⟩)
  show natDegree ((Equiv.Perm.sign σ).val • univ.prod fun i => M (σ i) i) ≤ n
  rw [← @Int.cast_smul_eq_zsmul ℝ ℝ[X] _ _ _ (Equiv.Perm.sign σ) (univ.prod fun i => M (σ i) i)]
  refine le_trans (natDegree_smul_le (Equiv.Perm.sign σ : ℝ) (univ.prod fun i => M (σ i) i))
    (le_trans (natDegree_prod_le _ _) (le_trans (sum_le_sum (fun i _ => h (σ i) i)) ?_))
  simp

include vContDiff s_isOpen in
lemma HairyBallTheorem.continuousOn_jac_f_apply {i j : Fin n} :
    ContinuousOn (fun x => jac_f x i j) s := by
  simp [LinearMap.toMatrix_apply]
  apply (PiLp.continuous_apply _ _ _).comp_continuousOn
  apply ContinuousOn.clm_apply
  · exact vContDiff.continuousOn_fderiv_of_isOpen s_isOpen le_rfl
  · fun_prop

lemma Polynomial.continuousOn_coeff_prod (P : Fin n → E n → ℝ[X])
    (hP : ∀ i k', ContinuousOn (fun x => (P i x).coeff k') s) (k : ℕ) :
    ContinuousOn (fun x => (∏ i, P i x).coeff k) s := by
  suffices ∀ m (h : m ≤ n), ContinuousOn
      (fun x => (∏ i, P (Fin.castLE h i) x).coeff k) s by
    convert this n le_rfl; simp
  intro m hm; induction m generalizing k with
  | zero => exact continuousOn_const
  | succ m ih =>
    simp [show m ≤ n by omega, forall_true_left] at ih
    simp [Fin.prod_univ_castSucc, coeff_mul]
    apply continuousOn_finsetSum; intro i _
    exact (ih _).fun_mul (hP _ _)

include vContDiff s_isOpen in
/-- det (f' t x) is polynomial in t and its coefficients are continuous in x. -/
lemma HairyBallTheorem.f't_det_poly : ∃ P : E n → Polynomial ℝ,
    (∀ x : E n, (P x).natDegree ≤ n)
    ∧ (∀ x : E n, (P x).coeff 0 = 1)
    ∧ (∀ t : ℝ, ∀ x : E n, (f' t x).det = (P x).eval t)
    ∧ (∀ k : ℕ, ContinuousOn (fun x => (P x).coeff k) s) := by
  let P := (fun x => (1 + (X : ℝ[X]) • (jac_f x).map C).det)
  use P
  constructor
  · refine fun x => natDegree_det _ (fun i j => ?_)
    simp [Matrix.one_apply]
    apply le_trans (natDegree_add_le _ _)
    rw [apply_ite natDegree, natDegree_one, natDegree_zero, ite_id, Nat.zero_max]
    apply le_trans natDegree_mul_le
    simp
  · and_intros
    · intro x
      dsimp [P]
      rw [coeff_zero_eq_eval_zero, eval_det]; simp
    · intro t x
      show LinearMap.det (f' t x : E n →ₗ[ℝ] E n) = eval t (P x)
      rw [← LinearMap.det_toMatrix (PiLp.basisFun _ _ _)]
      simp [P, eval_det, ← Matrix.op_smul_eq_mul_diagonal]
    · intro k
      have P_coeff : (fun x => (P x).coeff k)
          = (fun x => univ.sum (fun σ => Equiv.Perm.sign σ
          • (univ.prod (fun i => of (fun i j => (if i = j then 1 else 0)
          + C (jac_f x i j) * X) (σ i) i)).coeff k)) := by
        ext x
        dsimp [P]
        rw [det_apply, finsetSum_coeff]
        apply congrArg
        ext σ
        simp [Matrix.one_apply]
      rw [P_coeff]
      refine continuousOn_finsetSum _ (fun σ _ => ContinuousOn.const_smul
        (continuousOn_coeff_prod _ (fun i k' => ?_) _) _)
      by_cases hk'0 : k' = 0
      · simp [hk'0]; exact continuousOn_const
      by_cases hk'1 : k' = 1
      · simp [hk'1, apply_ite, ite_apply, coeff_one]
        exact HairyBallTheorem.continuousOn_jac_f_apply s_isOpen vContDiff
      simp [apply_ite, ite_apply, coeff_one, hk'0, coeff_X, hk'1, eq_comm]
      exact continuousOn_const

lemma HairyBallTheorem.pos_bound (M : ℝ) : ∀ᶠ t in 𝓝 0,
    0 < 1 - M * (range n).sum fun k => |t| ^ (k + 1) := by
  apply Filter.Tendsto.eventually_const_lt zero_lt_one
  apply Continuous.tendsto' (by fun_prop)
  simp

lemma HairyBallTheorem.range_bounded (ι : ℕ → ℝ) (m : ℕ) (hm : m > 0) (hι : ι 0 > 0) :
    ∃ M > 0, ∀ k ∈ range m, ι k ≤ M :=
  ⟨((range m).image ι).max' ((nonempty_range_iff.2 (by linarith)).image ι),
    by linarith [((range m).image ι).le_max' (ι 0) (mem_image_of_mem ι (mem_range.2 (by linarith)))],
    fun _ hk => le_max' _ _ (mem_image_of_mem ι hk)⟩

lemma HairyBallTheorem.unif_bounded_range_of_bounded {α : Type} (ι : ℕ → α → ℝ)
    (h : ∀ k, ∃ M, ∀ x, |ι k x| ≤ M) (m : ℕ) : ∃ M, ∀ k ∈ range m, ∀ x, |ι k x| ≤ M := by
  induction m with
  | zero => simp
  | succ m hm =>
    let ⟨M₀, hM₀⟩ := hm
    let ⟨M, hM⟩ := h m
    use max M M₀
    simp
    intro k k_le_m x
    by_cases hk : k = m
    · rw [hk]
      exact Or.inl (hM x)
    · exact Or.inr (hM₀ k (mem_range.2 (lt_of_le_of_ne k_le_m hk)) x)

include AComp hs in
lemma HairyBallTheorem.bound_poly (P : E n → Polynomial ℝ) (hdeg : ∀ x, (P x).natDegree ≤ n)
    (h0 : ∀ x, (P x).coeff 0 = 1) (hcont : ∀ k, ContinuousOn (fun x => (P x).coeff k) s) :
    ∃ M, ∀ t : ℝ, ∀ x : A,
    1 - M * ((range n).sum fun k => |t| ^ (k + 1)) ≤ (P x).eval t := by
  let continuous_coeff (k : ℕ) : C(A,ℝ) := ⟨_, ((hcont k).mono (subset_of_mem_nhdsSet hs)).domRestrict⟩
  let bounded_continuous_coeff (k : ℕ) := @BoundedContinuousFunction.mkOfCompact A ℝ _ _ (isCompact_iff_compactSpace.1 AComp) (continuous_coeff k)
  have : ∀ k, ∃ M, ∀ x : A, |(P x).coeff k| ≤ M :=
    fun k => ⟨‖bounded_continuous_coeff k‖, fun x => ((bounded_continuous_coeff k).norm_coe_le_norm x)⟩
  let ⟨M, hM⟩ := unif_bounded_range_of_bounded (fun k (x : A) => (P x).coeff k) this (m := n + 1)
  have : ∀ t, ∀ x : A, ∀ k ∈ range n, - M * |t| ^ (k + 1) ≤ ((P x).coeff (k + 1)) * t ^ (k + 1) := by
    refine fun t x k hk => le_trans ?_ (neg_abs_le _)
    simp [abs_mul, abs_pow]
    by_cases h₀ : t = 0
    · simp [h₀]
    · exact (mul_le_mul_iff_left₀ (pow_pos (abs_pos.2 h₀) _)).2 (hM (k + 1) (mem_range_succ_iff.2 (by linarith [mem_range.1 hk])) x)
  use M
  intro t x
  rw [(P x).eval_eq_sum_range' (lt_of_le_of_lt (hdeg x) (lt_add_one n)),
    sum_range_succ', h0 x,
    pow_zero, mul_one, sub_eq_neg_add, ← neg_mul, mul_sum]
  exact add_le_add_left (sum_le_sum (this t x)) _

include vContDiff AComp hs s_isOpen in
/-- det (f' t x) > 0 for sufficiently small t. -/
lemma HairyBallTheorem.zero_lt_det_f't : ∀ᶠ t in 𝓝 0, ∀ x : A, 0 < (f' t x).det := by
  have ⟨P, hP⟩ := f't_det_poly s_isOpen vContDiff
  have ⟨M, hM⟩ := bound_poly AComp hs P hP.1 hP.2.1 hP.2.2.2
  filter_upwards [pos_bound M] with t ht x
  rw [hP.2.2.1 t x]
  exact lt_of_lt_of_le ht (hM t x)

include vContDiff AComp hs s_isOpen in
/-- |det (f' t x)| is polynomial in t and its coefficients are continuous in x. -/
lemma HairyBallTheorem.abs_det_f't_poly : ∃ P : E n → Polynomial ℝ,
    (∀ x : E n, (P x).natDegree ≤ n)
    ∧ (∀ᶠ t in 𝓝 0, ∀ x : A, |(f' t x).det| = (P x).eval t)
    ∧ (∀ k : ℕ, ContinuousOn (fun x => (P x).coeff k) s) := by
  have ⟨P, hP⟩ := f't_det_poly s_isOpen vContDiff
  refine ⟨P, hP.1, ?_, hP.2.2.2⟩
  filter_upwards [zero_lt_det_f't AComp hs s_isOpen vContDiff] with t hpos x
  rw [abs_of_pos (hpos x), hP.2.2.1 t]

include vContDiff s_isOpen in
lemma HairyBallTheorem.continuousOn_abs_det_f't (t : ℝ) : ContinuousOn (fun x => |(f' t x).det|) s :=
  continuous_abs.comp_continuousOn (ContinuousLinearMap.continuous_det.comp_continuousOn
    (continuous_const.continuousOn.add (continuous_const.continuousOn.fun_smul
    (vContDiff.continuousOn_fderiv_of_isOpen s_isOpen (by rfl)))))

lemma HairyBallTheorem.nonneg_ae_abs_det_f't (t : ℝ) : 0 ≤ᵐ[volume.restrict A] fun x => |(f' t x).det| := by
  filter_upwards
  simp

include vContDiff AComp hs s_isOpen in
/-- the volume of (f t)''(A) is polynomial in t. -/
lemma HairyBallTheorem.vol_ft_A_poly : ∃ P : Polynomial ℝ, ∀ᶠ t in 𝓝 0,
    (volume ((f t) '' A)).toReal = (P.eval t) := by
  let ⟨P, hP⟩ := abs_det_f't_poly AComp hs s_isOpen vContDiff
  use (range (n + 1)).sum (fun i => C (∫ x in A, (P x).coeff i ∂volume) * X ^ i)
  filter_upwards [lintegral_abs_det_f't AComp hs vContDiff, hP.2.1] with t hInt hP1
  rw [← hInt, eval_finsetSum, ← integral_eq_lintegral_of_nonneg_ae (nonneg_ae_abs_det_f't t)
    (((continuousOn_abs_det_f't s_isOpen vContDiff t).mono (subset_of_mem_nhdsSet hs)).aestronglyMeasurable
    AComp.measurableSet)]
  have : A.EqOn (fun x => |(f' t x).det|) (fun x => (range (n + 1)).sum (fun n => (P x).coeff n * t ^ n)) := by
    intro x xA
    simp [hP1 ⟨x, xA⟩]
    nth_rw 1 [(P x).as_sum_range' (n + 1) (Nat.lt_succ_of_le (hP.1 x))]
    simp [eval_finsetSum]
  have integrable_coeff (i : ℕ) : Integrable (fun x => (P x).coeff i * t ^ i) (volume.restrict A) :=
    ContinuousOn.integrableOn_compact AComp (((hP.2.2 i).smul continuousOn_const).mono (subset_of_mem_nhdsSet hs))
  rw [setIntegral_congr_fun AComp.measurableSet this, integral_finsetSum _ (fun i _ => integrable_coeff i)]
  simp_rw [eval_mul, eval_C, eval_pow, eval_X, integral_mul_const]

end vol_poly


section image_ft_sphere

open Set

include hv in
lemma IsExtensionOfVectorFieldOnSn.inner_smul_self (t : ℝ) (x : E n) :
    ⟪x, t • v x⟫ = 0 := by
  rw [inner_smul_right, hv.isTang x, mul_zero]

include hv vUnit in
lemma HairyBallTheorem.ft_mem_sphere_of_mem_sphere (t : ℝ) (x : E n) (hx : x ∈ unitSphere n) :
    f t x ∈ Metric.sphere 0 (Real.sqrt (1 + t ^ 2)) := by
  rw [mem_sphere_zero_iff_norm, ← Real.sqrt_mul_self (norm_nonneg _),
    norm_add_sq_eq_norm_sq_add_norm_sq_real
    (hv.inner_smul_self t x)]
  simp [mem_sphere_zero_iff_norm.1 hx, norm_smul, vUnit x, sq]

include hv vUnit in
lemma HairyBallTheorem.image_ft_subset_sphere (t : ℝ) :
    (f t) '' (unitSphere n) ⊆ Metric.sphere 0 (Real.sqrt (1 + t ^ 2)) :=
  fun y ⟨x, hx, hxy⟩ => by
    rw [← hxy]
    exact ft_mem_sphere_of_mem_sphere hv vUnit t x hx

include hv vUnit in
lemma HairyBallTheorem.ft_mapsTo_sphere (t : ℝ) : MapsTo (f t) (unitSphere n)
    (Metric.sphere 0 (Real.sqrt (1 + t ^ 2))) :=
  fun x hx => ft_mem_sphere_of_mem_sphere hv vUnit t x hx

local notation "f_restr" =>
  fun (t : ℝ) ↦ restrictPreimage (Metric.sphere 0 (Real.sqrt (1 + t ^ 2))) (f t)

include hv in
lemma HairyBallTheorem.continuous_ft_restr (t : ℝ) : Continuous (f_restr t) :=
  (continuous_ft hv t).restrict _

include hv vUnit in
lemma HairyBallTheorem.ft_preimage_sphere (t : ℝ) :
    (f t) ⁻¹' (Metric.sphere 0 (Real.sqrt (1 + t ^ 2))) = unitSphere n := by
  ext x
  rw [mem_preimage, mem_sphere_zero_iff_norm,
    ← (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)),
    Real.sq_sqrt (add_nonneg (zero_le_one) (sq_nonneg _)),
    norm_add_sq_real, mem_sphere_zero_iff_norm, norm_smul, inner_smul_right,
    vUnit, hv.isTang, ← sq_abs t, Real.norm_eq_abs, ← mul_one (1 + _)]
  simp only [mul_zero, add_zero]
  have : ‖x‖ ^ 2 + (|t| * ‖x‖) ^ 2 = (1 + |t| ^ 2) * ‖x‖ ^ 2 := by ring
  rw [this, mul_eq_mul_left_iff, sq_eq_one_iff]
  simp only [(add_pos_of_pos_of_nonneg (zero_lt_one) (sq_nonneg |t|)).ne',
    (lt_of_lt_of_le neg_one_lt_zero (norm_nonneg _)).ne']
  simp

lemma Set.preimage_domRestrict {α β : Type} (s : Set α) (g : α → β) (t : Set β) :
    (domRestrict s g) ⁻¹' t = s ∩ (g ⁻¹' t) := by
  ext; simp [and_comm]

include vContDiff s_isOpen hs_crown in
lemma HairyBallTheorem.isOpenMap_ft : ∀ᶠ t in 𝓝 0, IsOpenMap (domRestrict (crown 2⁻¹ 2) (f t)) := by
  filter_upwards [zero_lt_det_f't (isCompact_closedCrown 2⁻¹ 2)
    hs_crown s_isOpen vContDiff] with t ht
  refine isOpenMap_iff_nhds_le.2 (fun ⟨x, hx⟩ => ?_)
  rw [domRestrict_apply, domRestrict_eq, ← Filter.map_map,
    ← @HasStrictFDerivAt.map_nhds_eq_of_equiv ℝ _ _ _ _ _ _ _ _
    ((f' t x).equivOfDetNeZero (ht ⟨x, Metric.crown_subset_closedCrown hx⟩).ne').toContinuousLinearEquiv _ _
    (ftStrictDeriv hs_crown vContDiff t x (Metric.crown_subset_closedCrown hx))]
  have : Filter.map Subtype.val (𝓝 (⟨x, hx⟩ : crown 2⁻¹ 2)) = 𝓝 x :=
    eq_of_le_of_ge continuous_subtype_val.continuousAt.tendsto
      (isOpenMap_iff_nhds_le.1 (Metric.isOpen_crown _ _).isOpenMap_subtype_val ⟨x, hx⟩)
  rw [this]

include hv vUnit in
lemma HairyBallTheorem.subtype_val_preimage_crown_eq_sphere (t : ℝ) :
    (univ : Set ((f t) ⁻¹' (Metric.sphere 0 (Real.sqrt (1 + t ^ 2)))))
    = Subtype.val ⁻¹' (crown 2⁻¹ 2) := by
  apply eq_preimage_subtype_val_iff.2
  rw [ft_preimage_sphere hv vUnit]
  refine fun x hx => ⟨fun _ => ?_, fun _ => mem_univ _⟩
  rw [Metric.mem_crown, mem_sphere_zero_iff_norm.1 hx]
  refine ⟨two_inv_lt_one, one_lt_two⟩

include hv vContDiff vUnit s_isOpen hs_crown in
/-- f t : unitSphere n → Metric.sphere 0 (sqrt (1 + t*t)) is open for sufficiently small t. -/
lemma HairyBallTheorem.isOpenMap_ft_restr : ∀ᶠ t in 𝓝 0, IsOpenMap (f_restr t) := by
  filter_upwards [isOpenMap_ft s_isOpen vContDiff hs_crown] with t ht
  intro U ⟨V, hV, hUV⟩
  have : U = Subtype.val ⁻¹' (V ∩ crown 2⁻¹ 2) := by
    rw [preimage_inter, hUV, ← subtype_val_preimage_crown_eq_sphere hv vUnit, inter_univ]
  rw [this, image_restrictPreimage, ← image_domRestrict]
  exact continuous_subtype_val.isOpen_preimage _
    (ht _ (continuous_subtype_val.isOpen_preimage _ hV))

include hv vUnit in
lemma HairyBallTheorem.image_ft_eq_image_ft_restr (t : ℝ) :
    (f t) '' (unitSphere n) = range (f_restr t) := by
  ext y
  refine ⟨fun ⟨x, hx, hxy⟩ => (mem_image _ _ _).2 ?_,
    fun ⟨y', ⟨x, hxy'⟩, hyy'⟩ => (mem_image _ _ _).2
    ⟨x, ⟨by simp [← ft_preimage_sphere hv vUnit t, Subtype.mem x],
    by simp [← hyy', ← hxy']⟩⟩⟩
  have y_mem_sphere : y ∈ Metric.sphere 0 (Real.sqrt (1 + t ^ 2)) := by
    rw [← hxy]
    exact ft_mem_sphere_of_mem_sphere hv vUnit t x hx
  use ⟨y, y_mem_sphere⟩
  exact ⟨mem_range.2 ⟨⟨x, by rwa [mem_preimage, hxy]⟩,
    Subtype.val_injective (by simp [hxy])⟩, by simp⟩

include hv vContDiff vUnit s_isOpen hs_crown in
lemma HairyBallTheorem.isOpen_image_ft_restr : ∀ᶠ t in 𝓝 0, IsOpen (range (f_restr t)) := by
  filter_upwards [isOpenMap_ft_restr hv vUnit s_isOpen vContDiff hs_crown] with t ht
  exact ht.isOpen_range

include hv in
lemma HairyBallTheorem.isClosed_image_ft (t : ℝ) : IsClosed ((f t) '' (unitSphere n)) :=
  ((isCompact_sphere _ _).image (continuous_ft hv t)).isClosed

include hv vUnit in
lemma HairyBallTheorem.isClosed_image_ft_restr (t : ℝ) : IsClosed (range (f_restr t)) :=
  (@isCompact_range _ _ _ _ (by rw [ft_preimage_sphere hv vUnit]; infer_instance) _
  (continuous_ft_restr hv t)).isClosed

lemma Set.image_val_preimage_val_eq_self {α : Type} (s : Set α) :
    Subtype.val '' (Subtype.val ⁻¹' s : Set s) = s := by
  rw [Subtype.image_preimage_coe, inter_self]

include hn hv vContDiff vUnit s_isOpen hs_crown in
lemma HairyBallTheorem.image_ft_eq_sphere : ∀ᶠ t in 𝓝 0,
    (f t) '' (unitSphere n) = Metric.sphere 0 (Real.sqrt (1 + t  ^ 2)) := by
  filter_upwards [isOpen_image_ft_restr hv vUnit s_isOpen
    vContDiff hs_crown] with t ht
  apply eq_of_subset_of_subset (@image_ft_subset_sphere _ _ hv vUnit t)
  rw [image_ft_eq_image_ft_restr hv vUnit]
  nth_rw 1 [← (Metric.sphere _ _).image_val_preimage_val_eq_self]
  apply (image_subset_image_iff Subtype.val_injective).2
  rw [Subtype.coe_preimage_self]
  refine (Subtype.connectedSpace
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simpa)) _ (Real.sqrt_nonneg _))).isPreconnected_univ.subset_isClopen
    ⟨isClosed_image_ft_restr hv vUnit t, ht⟩ ?_
  rw [univ_inter]
  apply Nonempty.of_image
  rw [← @image_ft_eq_image_ft_restr _ _ hv vUnit]
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 (by linarith)
  apply ((NormedSpace.sphere_nonempty).2 (zero_le_one)).image

include hn hv vContDiff vUnit s_isOpen hs_crown in
lemma HairyBallTheorem.image_ft_sphere_eq_sphere : ∀ᶠ t in 𝓝 0, ∀ r > 0,
    (f t) '' (Metric.sphere 0 r) = Metric.sphere 0 (r * Real.sqrt (1 + t  ^ 2)) := by
  filter_upwards [image_ft_eq_sphere hn hv vUnit s_isOpen vContDiff hs_crown] with t ht r r_pos
  refine eq_of_subset_of_subset
    (fun y ⟨x, hx, hxy⟩ => mem_sphere_zero_iff_norm.2
    (mul_left_cancel₀ (inv_pos.2 r_pos).ne' ?_))
    (fun y hy => ?_)
  · rw [← mul_assoc, inv_mul_cancel₀ r_pos.ne', one_mul, ← abs_eq_self.2 r_pos.le,
      ← abs_inv, ← Real.norm_eq_abs,  ← norm_smul, ← mem_sphere_zero_iff_norm, ← ht]
    refine ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.2 ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀]
      rw [mem_sphere_zero_iff_norm.1 hx]
      exact r_pos.ne'
    · simp only [mem_sphere_zero_iff_norm.1 hx, ← hxy,
        hv.isExtension _ _ (inv_nonneg.2 r_pos.le), smul_add, smul_smul, mul_comm]
  · have : r⁻¹ • y ∈ Metric.sphere 0 √(1 + t ^ 2) := by
      apply mem_sphere_zero_iff_norm.2
      rw [norm_smul, mem_sphere_zero_iff_norm.1 hy, norm_inv, Real.norm_eq_abs,
        abs_eq_self.2 r_pos.le, ← mul_assoc, inv_mul_cancel₀ r_pos.ne', one_mul]
    rw [← ht] at this
    let ⟨x, hx, hxy⟩ := this
    refine ⟨r • x, by rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_eq_self.2 r_pos.le, mem_sphere_zero_iff_norm.1 hx, mul_one], ?_⟩
    simp only [hv.isExtension _ _ r_pos.le]
    simp only at hxy
    rw [smul_smul, mul_comm, ← smul_smul, ← smul_add, hxy, smul_smul,
      mul_inv_cancel₀ r_pos.ne', one_smul]

end image_ft_sphere


section volume_closedCrown

open Set Metric MeasureTheory

include n_pos in
lemma measure_closedCrown {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (volume (closedCrown a b)).toReal = (b ^ n - a ^ n) * (volume (ball (0 : E n) 1)).toReal := by
  have := Fin.pos_iff_nonempty.1 n_pos
  rw [measure_sdiff ((ball_subset_ball hab).trans ball_subset_closedBall)
    measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne,
    Measure.addHaar_closedBall _ _ (ha.trans hab), Measure.addHaar_ball _ _ ha,
    finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_sub_of_le
    ((ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne).2
    (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ha hab n)))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)]
  simp [ENNReal.toReal_ofReal (pow_nonneg ha _),
    ENNReal.toReal_ofReal (pow_nonneg (ha.trans hab) _), sub_mul]

include n_pos in
lemma measure_closedCrown_ne_zero {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (volume (closedCrown a b)).toReal ≠ 0 := by
  rw [measure_closedCrown n_pos ha hab.le]
  exact mul_ne_zero (sub_ne_zero.2 (not_imp_not.2 (pow_eq_pow_iff_of_ne_zero n_pos.ne').1
    (not_or.2 ⟨hab.ne', not_and_or.2 (Or.inl (by linarith))⟩)))
    (ENNReal.toReal_ne_zero.2 ⟨(measure_ball_pos _ _ one_pos).ne', measure_ball_lt_top.ne⟩)

lemma closedCrown_eq_union_sphere (a b : ℝ) : closedCrown a b = ⋃ (r : Icc a b), sphere 0 r := by
  refine eq_of_subset_of_subset
    (fun x ⟨hxb, hxa⟩ => mem_iUnion.2
    ⟨⟨‖x‖, ⟨not_lt.1 (fun h => hxa (mem_ball_zero_iff.2 h)),
    mem_closedBall_zero_iff.1 hxb⟩⟩, mem_sphere_zero_iff_norm.2 rfl⟩)
    (fun x hx => ?_)
  let ⟨r, hr⟩ := mem_iUnion.1 hx
  let ⟨hra, hrb⟩ := r.2
  rw [← mem_sphere_zero_iff_norm.1 hr] at hra
  rw [← mem_sphere_zero_iff_norm.1 hr] at hrb
  exact ⟨mem_closedBall_zero_iff.2 hrb,
    mem_compl (fun h => not_lt.2 hra (mem_ball_zero_iff.1 h))⟩

lemma Real.sqrt_one_add_sq_pos {t : ℝ} : 0 < √(1 + t ^ 2) := by positivity

include hn hv vContDiff vUnit s_isOpen hs_crown in
lemma HairyBallTheorem.image_ft_closedCrown_eq_closedCrown (a b : ℝ) (ha : 0 < a) : ∀ᶠ t in 𝓝 0,
    (f t) '' (closedCrown a b) = closedCrown (a * √(1 + t ^ 2)) (b * √(1 + t ^ 2)) := by
  filter_upwards [image_ft_sphere_eq_sphere hn hv vUnit s_isOpen vContDiff hs_crown] with t ht
  simp only [closedCrown_eq_union_sphere]
  rw [image_iUnion]
  refine eq_of_subset_of_subset (fun y hy => ?_) ?_
  · let ⟨r, ⟨x, hxr, hxy⟩⟩ := mem_iUnion.1 hy
    refine mem_iUnion.2 ⟨⟨r * √(1 + t ^ 2),
      ⟨(mul_le_mul_iff_left₀ t.sqrt_one_add_sq_pos).2 r.2.1,
      (mul_le_mul_iff_left₀ t.sqrt_one_add_sq_pos).2 r.2.2⟩⟩, ?_⟩
    dsimp; rw [← ht _ (lt_of_lt_of_le ha r.2.1)]
    use x
  · intro x hx
    let ⟨r, hr⟩ := mem_iUnion.1 hx
    refine mem_iUnion.2 ⟨⟨r.1 * (√(1 + t ^ 2))⁻¹,
      ⟨(le_mul_inv_iff₀ t.sqrt_one_add_sq_pos).2 r.2.1,
      (mul_inv_le_iff₀ t.sqrt_one_add_sq_pos).2 r.2.2⟩⟩, ?_⟩
    rwa [ht _ (mul_pos (lt_of_lt_of_le (mul_pos ha Real.sqrt_one_add_sq_pos) r.2.1)
      (inv_pos_of_pos t.sqrt_one_add_sq_pos)), mul_assoc,
      inv_mul_cancel₀ t.sqrt_one_add_sq_pos.ne', mul_one]

include hn hv vContDiff vUnit s_isOpen hs_crown in
lemma HairyBallTheorem.volume_image_closedCrown {a b : ℝ} (ha : 0 < a) (hab : a ≤ b): ∀ᶠ t in 𝓝 0,
    (volume ((f t) '' (closedCrown a b))).toReal = √(1 + t ^ 2) ^ n * (volume (closedCrown a b)).toReal := by
  filter_upwards [image_ft_closedCrown_eq_closedCrown hn hv vUnit s_isOpen vContDiff hs_crown a b ha] with t ht
  rw [ht, measure_closedCrown (one_pos.trans hn) ha.le hab, ← mul_assoc, mul_sub, ← mul_pow, ← mul_pow,
    measure_closedCrown (one_pos.trans hn) (mul_nonneg ha.le (Real.sqrt_nonneg _))
    ((mul_le_mul_iff_left₀ t.sqrt_one_add_sq_pos).2 hab)]
  ac_rfl

end volume_closedCrown


section sq_ne_poly

open Polynomial

lemma Polynomial.funext_nhds_zero_ne_zero {P Q : ℝ[X]} : P = Q ↔ ∀ᶠ t in 𝓝 0, t ≠ 0 → P.eval t = Q.eval t := by
  refine ⟨fun h => Filter.Eventually.of_forall fun _ _ => by rw [h],
    fun h => eq_of_infinite_eval_eq _ _ ?_⟩
  obtain ⟨t, ht⟩ := eventually_nhds_iff.1 h
  have : t \ {0} ⊆ {x | eval x P = eval x Q} :=
    fun x hx => ht.1 x hx.1 hx.2
  exact Set.Infinite.mono this (Set.Infinite.sdiff
    (infinite_of_mem_nhds 0 (ht.2.1.mem_nhds ht.2.2)) (Set.finite_singleton _))

lemma Polynomial.not_one_add_X_sq_eq_sq : ¬ (∃ P : ℝ[X], 1 + X ^ 2 = P ^ 2) := by
  intro ⟨P, hP⟩
  have P_natDegree_eq_one : P.natDegree = 1 := by
    apply mul_left_cancel₀ two_ne_zero
    rw [← natDegree_pow, ← hP, ← C_1, natDegree_C_add, natDegree_pow, natDegree_X]
  let ⟨a, b, hab⟩ := (exists_eq_X_add_C_of_natDegree_le_one (by rw [P_natDegree_eq_one]) :
    ∃ a b, P = C a * X + C b)
  rw [hab] at hP
  have h0 := congrArg (coeff · 0) hP
  have h1 := congrArg (coeff · 1) hP
  simp [sq] at h0
  simp [add_sq, mul_pow, coeff_mul_X_pow', ← map_pow] at h1
  rw [← C_1, coeff_C_of_ne_zero (one_ne_zero)] at h1
  have a0 : a = 0 :=
    mul_left_cancel₀ two_ne_zero ((mul_right_cancel₀
      (left_ne_zero_of_mul (ne_zero_of_eq_one h0.symm))) (by simp [← h1]))
  rw [hab, a0, C_0, zero_mul, zero_add, natDegree_C] at P_natDegree_eq_one
  exact zero_ne_one P_natDegree_eq_one

lemma not_sqrt_one_add_sq_eq_poly :
    ¬ (∃ P : Polynomial ℝ, ∀ᶠ t in 𝓝 0, t ≠ 0 → Real.sqrt (1 + t ^ 2) = P.eval t) := by
  refine fun ⟨P, hP⟩ => not_one_add_X_sq_eq_sq ⟨P, funext_nhds_zero_ne_zero.2 ?_⟩
  filter_upwards [hP] with t ht t0
  simp [← ht t0, Real.sq_sqrt (add_nonneg (zero_le_one) (sq_nonneg _))]

lemma continuous_one_add_sq_rpow (k : ℝ) (hk : 0 ≤ k) : Continuous (fun t : ℝ => (1 + t ^ 2) ^ k) := by
  fun_prop (disch := assumption)

lemma continuous_mul_id_mul_one_add_sq_rpow (m : ℕ) :
    Continuous (fun t : ℝ => (2 * m + 3) * t * (1 + t ^ 2) ^ ((2 * m + 1) / 2 : ℝ)) :=
  (continuous_const.mul continuous_id).mul (continuous_one_add_sq_rpow _
    (div_nonneg (by linarith) zero_le_two))

lemma deriv_one_add_sq_pow (m : ℕ) :
    deriv (fun t => (1 + t ^ 2) ^ ((2 * (m + 1) + 1 : ℝ) / 2))
    = (fun t : ℝ => (2 * m + 3) * t * (1 + t ^ 2) ^ ((2 * m + 1 : ℝ) / 2)) := by
  ext x
  rw [deriv_rpow_const (by fun_prop) (by left; positivity)]
  simp only [differentiableAt_const, differentiableAt_fun_id, DifferentiableAt.fun_pow,
    deriv_fun_add, deriv_const', deriv_fun_pow, deriv_id'']
  ring_nf

include odd_n in
lemma not_one_add_sq_pow_n_div_two_eq_poly :
    ¬ ∃ P : Polynomial ℝ, ∀ᶠ t in 𝓝 0, (1 + t ^ 2) ^ (n / 2 : ℝ) = P.eval t := by
  suffices ¬ ∃ P : Polynomial ℝ, ∀ᶠ t in 𝓝 0, t ≠ 0 → (1 + t ^ 2) ^ (n / 2 : ℝ) = P.eval t by
    refine not_imp_not.mpr (Exists.imp fun P h => ?_) this
    filter_upwards [h] with t ht _
    exact ht
  let ⟨m, hm⟩ := odd_n
  rw [hm]
  clear hm
  induction m <;> intro ⟨P, hP⟩
  · simp only [mul_zero, zero_add, Nat.cast_one, ← Real.sqrt_eq_rpow] at hP
    exact not_sqrt_one_add_sq_eq_poly ⟨P, hP⟩
  · rename_i m ih
    obtain ⟨s, hs⟩ := eventually_nhds_iff.1 hP
    have : (fun t => (1 + t ^ 2) ^ ((2 * (m + 1) + 1 : ℝ) / 2))
        =ᶠ[𝓝 0] (fun t => eval t P) := by
      refine eventually_nhds_iff.2 ⟨s, ?_, hs.2⟩
      exact Set.EqOn.of_subset_closure (s := s \ {0})
        (fun x hx => by exact_mod_cast hs.1 x hx.1 hx.2)
        (ContinuousOn.rpow_const (by fun_prop) (fun x _ => Or.inr (div_nonneg (by linarith) zero_le_two)))
        P.continuous.continuousOn Set.sdiff_subset
        ((dense_compl_singleton _).open_subset_closure_inter hs.2.1)
    have : (fun t : ℝ => (2 * m + 3) * t * (1 + t ^ 2) ^ ((2 * m + 1 : ℝ) / 2))
        =ᶠ[𝓝 0] (fun t => eval t (derivative P)) := by
      rw [← _root_.funext (fun x => Polynomial.deriv _), ← deriv_one_add_sq_pow]
      exact Filter.EventuallyEq.deriv this
    have derivative_coeff_zero : (derivative P).coeff 0 = 0 := by
      simp [coeff_zero_eq_eval_zero, ← Filter.EventuallyEq.eq_of_nhds this]
    have X_mul_divX_derivative : derivative P = X * divX (derivative P) := by
      rw [← add_zero (_ * _), ← C_0, ← derivative_coeff_zero, X_mul_divX_add]
    rw [X_mul_divX_derivative] at this
    refine ih ⟨C (1 / (2 * m + 3) : ℝ) * divX (derivative P), ?_⟩
    filter_upwards [this] with t ht t0
    rw [eval_mul, eval_C]
    apply mul_left_cancel₀ (by linarith : 2 * (m : ℝ) + 3 ≠ 0)
    rw [← mul_assoc, mul_div_cancel₀ _ (by linarith), one_mul]
    apply mul_left_cancel₀ t0
    nth_rw 3 [← @eval_X _ _ t]
    rw [← eval_mul, ← ht]
    norm_cast
    ac_rfl

end sq_ne_poly


open Polynomial

include hn odd_n hv vUnit in
lemma HairyBallTheorem.contradiction (hvs_crown : ContDiffOn ℝ 1 v {0}ᶜ) : False := by
  let ⟨P, hP⟩ := vol_ft_A_poly (isCompact_closedCrown _ _)
    (isOpen_compl_singleton.mem_nhdsSet.2 (by simp : closedCrown 1 2 ⊆ {0}ᶜ))
    isOpen_compl_singleton hvs_crown
  refine not_one_add_sq_pow_n_div_two_eq_poly odd_n
    ⟨P * C (MeasureTheory.volume (closedCrown 1 2)).toReal⁻¹, ?_⟩
  filter_upwards [hP, volume_image_closedCrown hn hv vUnit isOpen_compl_singleton
    hvs_crown (isOpen_compl_singleton.mem_nhdsSet.2 (by simp : closedCrown 2⁻¹ 2 ⊆ {0}ᶜ))
    one_pos one_le_two] with t ht1 ht2
  rw [eval_mul, eval_C, ← ht1, ht2, Real.sqrt_eq_rpow, ← Real.rpow_natCast _ n,
    ← Real.rpow_mul (by positivity), one_div_mul_eq_div,
    mul_assoc, mul_inv_cancel₀ (measure_closedCrown_ne_zero (one_pos.trans hn) zero_le_one one_lt_two), mul_one]

include hv in
lemma IsExtensionOfVectorVieldOnSn.v_zero : v 0 = 0 := by
  rw [← zero_smul ℝ 0, hv.isExtension _ _ (le_refl _), zero_smul, zero_smul]

lemma mem_unitSphere_of_ne_zero {x : E n} (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ unitSphere n := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]

include hn odd_n in
theorem hairy_ball_diff (contDiff_v : ContDiff ℝ 1 v)
    (isTang_v : ∀ x : unitSphere n, ⟪v x, x⟫ = 0) : ∃ x ∈ unitSphere n, v x = 0 := by
  by_contra!
  have v_ne_zero : ∀ x, x ≠ 0 → v (‖x‖⁻¹ • x) ≠ 0 :=
    fun _ hx => this _ (mem_unitSphere_of_ne_zero hx)
  let v' : E n → E n := fun x => ‖x‖ • ‖v (‖x‖⁻¹ • x)‖⁻¹ • v (‖x‖⁻¹ • x)
  have contDiffOn_v : ContDiffOn ℝ 1 (fun x => v (‖x‖⁻¹ • x)) {0}ᶜ :=
    contDiff_v.comp_contDiffOn (ContDiffOn.smul ((contDiffOn_inv ℝ).comp
    (ContDiffOn.norm ℝ contDiffOn_id (fun _ => id)) (fun _ => by simp; exact id)) contDiffOn_id)
  have v'ContDiff : ContDiffOn ℝ 1 v' {0}ᶜ :=
    ContDiffOn.smul (fun x hx => (contDiffAt_norm ℝ hx).contDiffWithinAt)
    (ContDiffOn.smul ((contDiffOn_inv ℝ).comp (ContDiffOn.norm ℝ contDiffOn_v v_ne_zero)
    (fun x hx => norm_ne_zero_iff.2 (v_ne_zero x hx))) contDiffOn_v)
  have hv' : IsExtensionOfVectorFieldOnSn _ v' := by
    constructor
    · refine continuous_iff_continuousAt.2 (fun x => ?_)
      by_cases hx : x = 0
      · rw [hx]
        unfold ContinuousAt v'
        rw [norm_zero, zero_smul]
        refine Filter.Tendsto.zero_smul_isBoundedUnder_le tendsto_norm_zero
          (Filter.isBoundedUnder_of ⟨1, fun y => ?_⟩)
        rw [Function.comp_apply, norm_smul, norm_inv, norm_norm]
        exact inv_mul_le_one
      · exact ContinuousOn.continuousAt v'ContDiff.continuousOn (compl_singleton_mem_nhds hx)
    · intro x
      by_cases hx : x = 0
      · rw [hx, inner_zero_left]
      · rw [inner_smul_right, inner_smul_right, ← one_mul ⟪_, _⟫,
          ← mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), mul_assoc, ← real_inner_smul_left,
          real_inner_comm, isTang_v ⟨_, mem_unitSphere_of_ne_zero hx⟩]
        simp only [mul_zero]
    · intro x r hr
      unfold v'
      by_cases hr' : r = 0
      · simp [hr']
      rw [norm_smul, Real.norm_eq_abs, abs_eq_self.2 hr.le, mul_inv, mul_smul, mul_smul,
        ← mul_smul _ r, mul_comm, ← mul_smul r⁻¹, ← mul_assoc, inv_mul_cancel₀ hr', one_mul]
  have v'Unit : ∀ x, ‖v' x‖ = ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · rw [hx, norm_smul, norm_zero, norm_zero, zero_mul]
    · rw [norm_smul, norm_smul, norm_inv, norm_norm, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 (v_ne_zero _ hx)), mul_one]
  exact @HairyBallTheorem.contradiction _ hn odd_n _ hv' v'Unit v'ContDiff

end



section

open MvPolynomial

variable {σ : Type*} {R : Type*}

namespace MvPolynomial

variable [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

@[simps]
noncomputable def toContinuousMap (p : MvPolynomial σ R) : C(σ → R, R) :=
  ⟨fun x => eval x p, by continuity⟩

@[simps]
noncomputable def toContinuousMapOn (p : MvPolynomial σ R) (X : Set (σ → R)) : C(X, R) :=
  ⟨fun x => p.toContinuousMap x, by fun_prop⟩

@[simps]
noncomputable def toContinuousMapAlgHom : MvPolynomial σ R →ₐ[R] C(σ → R, R) where
  toFun p := p.toContinuousMap
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  commutes' _ := by ext; simp

@[simps]
noncomputable def toContinuousMapOnAlgHom (X : Set (σ → R)): MvPolynomial σ R →ₐ[R] C(X, R) where
  toFun p := p.toContinuousMapOn X
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp
  commutes' _ := by ext; simp

end MvPolynomial

section

variable [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

noncomputable def mvPolynomialFunctions (X : Set (σ → R)) : Subalgebra R C(X, R) :=
  (⊤ : Subalgebra R (MvPolynomial σ R)).map (MvPolynomial.toContinuousMapOnAlgHom X)

theorem mvPolynomialFunctions_separatesPoints (X : Set (σ → R)) :
    (mvPolynomialFunctions X).SeparatesPoints := by
  intro x y h
  obtain ⟨s, hs⟩ := Classical.exists_not_of_not_forall
    (not_imp_not.mpr funext_iff.mpr (Subtype.coe_ne_coe.mpr h))
  exact ⟨_, ⟨_, ⟨MvPolynomial.X s, ⟨Algebra.mem_top, rfl⟩⟩, rfl⟩, by simp [hs]⟩

theorem mvPolynomialFunctions.topologicalClosure (X : Set (σ → ℝ)) [CompactSpace X] :
    (mvPolynomialFunctions X).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (mvPolynomialFunctions_separatesPoints X)

theorem mvPolynomialFunctions.starClosure_topologicalClosure {𝕜 : Type*} [RCLike 𝕜]
    (X : Set (σ → 𝕜)) [CompactSpace X] :
    (mvPolynomialFunctions X).starClosure.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (Subalgebra.separatesPoints_monotone le_sup_left (mvPolynomialFunctions_separatesPoints X))

theorem continuousMap_mem_mvPolynomialFunctions_closure (X : Set (σ → ℝ)) [CompactSpace X]
    (f : C(X, ℝ)) :
    f ∈ (mvPolynomialFunctions X).topologicalClosure := by
  rw [mvPolynomialFunctions.topologicalClosure]
  simp

theorem exists_mvPolynomial_near_continuousMap (X : Set (σ → ℝ)) [CompactSpace X]
    (f : C(X, ℝ)) (ε : ℝ) (pos : 0 < ε) :
    ∃ p : MvPolynomial σ ℝ, ‖p.toContinuousMapOn _ - f‖ < ε := by
  have w := mem_closure_iff_frequently.mp (continuousMap_mem_mvPolynomialFunctions_closure _ f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨-, H, ⟨m, ⟨-, rfl⟩⟩⟩ := w ε pos
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨m, H⟩

theorem exists_mvPolynomial_near_of_continuous (X : Set (σ → ℝ)) [CompactSpace X]
    (f : X → ℝ) (c : Continuous f) (ε : ℝ) (pos : 0 < ε) :
    ∃ p : MvPolynomial σ ℝ, ∀ x : X, |eval x p - f x| < ε := by
  obtain ⟨p, b⟩ := exists_mvPolynomial_near_continuousMap _ ⟨f, c⟩ ε pos
  use p
  rwa [ContinuousMap.norm_lt_iff _ pos] at b

end

end



section

open MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {x : ι → 𝕜}

namespace MvPolynomial

variable (p : MvPolynomial ι 𝕜)

omit [DecidableEq ι] in
lemma prod_pow_support (u : ι →₀ ℕ) (x : ι → 𝕜) :
    ∏ i : ι, x i ^ u i = ∏ i ∈ u.support, x i ^ u i := by
  rw [Finset.prod_subset u.support.subset_univ (fun i _ hi => ?_)]
  rw [Finsupp.notMem_support_iff.1 hi, pow_zero]

omit [DecidableEq ι] in
lemma sum_smul_support {R M : Type} [AddCommMonoid M] [Semiring R] [Module R M]
    (u : ι →₀ R) (g : ι → M) :
    ∑ i : ι, u i • g i = ∑ i ∈ u.support, u i • g i := by
  rw [Finset.sum_subset u.support.subset_univ (fun i _ hi => ?_)]
  rw [Finsupp.notMem_support_iff.1 hi, zero_smul]

theorem hasStrictFDerivAt_monomial {u : ι →₀ ℕ} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => ∏ i : ι, x i ^ u i)
    (∑ i ∈ u.support, (∏ j ∈ u.support.erase i, x j ^ u j) • u i • x i ^ (u i - 1)
    • ContinuousLinearMap.proj i) x := by
  rw [funext (prod_pow_support u)]
  refine HasStrictFDerivAt.finsetProd (fun i _ => ?_)
  have : (u i • x i ^ (u i - 1) • ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ => 𝕜) i) =
      (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (u i * x i ^ (u i - 1))).comp (ContinuousLinearMap.proj i) := by
    ext x
    simp [mul_comm, mul_assoc]
  rw [this]
  exact HasStrictFDerivAt.comp x (hasStrictDerivAt_pow (u i) (x i)).hasStrictFDerivAt
    (hasStrictFDerivAt_apply i x)

theorem hasStrictFDerivAt_monomial' {u : ι →₀ ℕ} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => ∏ i : ι, x i ^ u i)
    (∑ i ∈ u.support, (∏ j ∈ u.support.erase i, x j ^ u j)
    • (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (u i * x i ^ (u i - 1))).comp
    (ContinuousLinearMap.proj i)) x := by
  rw [funext (prod_pow_support u)]
  exact HasStrictFDerivAt.finsetProd (fun i _ => HasStrictFDerivAt.comp x
    (hasStrictDerivAt_pow (u i) (x i)).hasStrictFDerivAt (hasStrictFDerivAt_apply i x))

theorem hasStrictFDerivAt_monomial'' {u : ι →₀ ℕ} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => ∏ i ∈ u.support, x i ^ u i)
    (∑ i ∈ u.support, (∏ j ∈ u.support.erase i, x j ^ u j)
    • (ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (u i * x i ^ (u i - 1))).comp
    (ContinuousLinearMap.proj i)) x :=
  HasStrictFDerivAt.finsetProd (fun i _ => HasStrictFDerivAt.comp x
    (hasStrictDerivAt_pow (u i) (x i)).hasStrictFDerivAt (hasStrictFDerivAt_apply i x))

lemma prod_sub_single_eq_prod_erase_mul {u : ι →₀ ℕ} {i : ι} (hi : i ∈ u.support) :
    ∏ j : ι, x j ^ (u j - Finsupp.single i 1 j)
    = (∏ j ∈ u.support.erase i, x j ^ u j) * x i ^ (u i - 1) := by
  rw [← Finset.prod_subset u.support.subset_univ (fun j _ hj => ?_),
    ← Finset.prod_erase_mul _ _ hi, Finsupp.single_apply, ite_eq_left rfl,
    Finset.prod_congr rfl (fun j hj => ?_)]
  rw [Finsupp.single_apply, ite_eq_right (Finset.ne_of_mem_erase hj).symm, tsub_zero]
  rw [Finsupp.single_apply, ite_eq_right (fun h => hj (by rwa [← h])), tsub_zero,
    Finsupp.notMem_support_iff.1 hj, pow_zero]

theorem hasStrictFDerivAt_monomial''' {u : ι →₀ ℕ} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => ∏ i : ι, x i ^ u i)
    (∑ i : ι, u i • (∏ j : ι, x j ^ (u j - (Finsupp.single i 1) j))
    • (ContinuousLinearMap.proj i)) x := by
  rw [sum_smul_support u _, Finset.sum_congr rfl (fun i hi =>
    by rw [prod_sub_single_eq_prod_erase_mul hi, smul_comm, mul_smul, ← smul_comm (u i)])]
  exact hasStrictFDerivAt_monomial

protected theorem hasStrictFDerivAt :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x => eval x p)
    (∑ i : ι, (eval x (pderiv i p)) • (ContinuousLinearMap.proj i)) x := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    simp only [eval_monomial, Finsupp.prod_pow, pderiv_monomial, Finsupp.coe_tsub,
      Pi.sub_apply, mul_smul, ← Finset.smul_sum]
    apply HasStrictFDerivAt.const_mul
    rw [Finset.sum_congr rfl (fun _ _ => Nat.cast_smul_eq_nsmul _ _ _)]
    exact hasStrictFDerivAt_monomial'''
  | add p q hp hq =>
    simp only [map_add]
    rw [Finset.sum_congr rfl (fun _ _ => add_smul _ _ _), Finset.sum_add_distrib]
    exact hp.add hq

protected theorem hasFDerivAt  :
    HasFDerivAt (𝕜 := 𝕜) (fun x => eval x p)
    (∑ i : ι, (eval x (pderiv i p)) • (ContinuousLinearMap.proj i)) x :=
  p.hasStrictFDerivAt.hasFDerivAt

protected theorem differentiableAt :
    DifferentiableAt 𝕜 (fun x => eval x p) x :=
  p.hasStrictFDerivAt.differentiableAt

protected theorem differentiable : Differentiable 𝕜 (fun x => eval x p) :=
  fun _ => p.differentiableAt

@[simp]
protected theorem fderiv : fderiv 𝕜 (fun x => eval x p) x
    = ∑ i : ι, (eval x (pderiv i p)) • (ContinuousLinearMap.proj i) :=
  p.hasFDerivAt.fderiv

lemma contDiff_one : ContDiff 𝕜 1 (fun x => eval x p) := by
  refine contDiff_one_iff_fderiv.2 ⟨p.differentiable, ?_⟩
  show Continuous (fun x => fderiv 𝕜 (fun x => eval x p) x)
  rw [funext (fun x => p.fderiv)]
  continuity

end MvPolynomial

end



section

variable (odd_n : Odd n) {v : unitSphere n → E n} (continuous_v : Continuous v)
  (isTang_v : ∀ x : unitSphere n, ⟪v x, x⟫ = 0)

variable {n}

lemma norm_sub_proj_le_norm (x : unitSphere n) (y : E n) : ‖y - ⟪y, x⟫ • x‖ ≤ ‖y‖ := by
  rw [← abs_eq_self.2 (norm_nonneg _), ← abs_eq_self.2 (norm_nonneg y), ← sq_le_sq,
    norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    mem_sphere_zero_iff_norm.1 x.2]
  ring_nf
  exact sub_le_self _ (sq_nonneg _)

lemma norm_sub_proj_sub_le_norm_of_inner_eq_zero (x : unitSphere n) (y z : E n) (h : ⟪z, x⟫ = 0) :
    ‖y - ⟪y, x⟫ • x - z‖ ≤ ‖y - z‖ := by
  rw [← sub_zero (inner _ _ _), ← h, ← inner_sub_left, sub_right_comm]
  exact norm_sub_proj_le_norm _ _

lemma contDiff_proj {v : E n → E n} (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (fun x => v x - ⟪v x, x⟫ • x) :=
  hv.sub (ContDiff.smul ((hv.inner ℝ) contDiff_id) contDiff_id)

include hn odd_n continuous_v isTang_v in
lemma exists_near_v_vanishing (ε : ℝ) (hε : 0 < ε) : ∃ v' : unitSphere n → E n,
    (∀ x, ‖v' x - v x‖ < ε) ∧ (∃ x, v' x = 0) := by
  have inst : CompactSpace (WithLp.ofLp '' unitSphere n) :=
    isCompact_iff_compactSpace.mp ((isCompact_sphere ..).image (PiLp.continuous_ofLp ..))
  choose p hp using (fun i => exists_mvPolynomial_near_of_continuous (WithLp.ofLp '' unitSphere n)
    (fun x => (v ⟨WithLp.toLp 2 x, by have ⟨y, hy, hx⟩ := (Set.mem_image ..).mp x.prop; rwa [← hx, WithLp.toLp_ofLp]⟩).ofLp i)
    (by fun_prop) ((√n)⁻¹ * ε)
    (mul_pos (inv_pos.2 (Real.sqrt_pos_of_pos (Nat.cast_pos'.2 odd_n.pos))) hε))
  let q : E n → E n := fun x => WithLp.toLp 2 fun i => MvPolynomial.eval x (p i)
  refine ⟨(fun (x : unitSphere n) => (q x - ⟪q x, x⟫ • x)), fun x => ?_, ?_⟩
  · apply lt_of_le_of_lt (norm_sub_proj_sub_le_norm_of_inner_eq_zero _ _ _ (isTang_v x))
    rw [EuclideanSpace.norm_eq, Real.sqrt_lt' hε, ← one_mul ε,
      ← congrArg (· * ε) (mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 (Nat.cast_pos'.2 odd_n.pos))),
      mul_assoc, mul_pow, Real.sq_sqrt n.cast_nonneg', ← nsmul_eq_mul, ← Fin.sum_const]
    refine Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2
      (Fin.pos_iff_nonempty.mp odd_n.pos)) (fun i _ => sq_lt_sq.2 ?_)
    rw [Real.norm_eq_abs, abs_abs, PiLp.sub_apply, abs_mul, abs_eq_self.2 hε.le,
      abs_eq_self.2 (inv_nonneg.2 (Real.sqrt_nonneg _))]
    have := hp i ⟨WithLp.ofLp x, Set.mem_image_of_mem _ (by exact x.prop)⟩
    simpa using this
  · suffices ∃ x : E n, x ∈ unitSphere n ∧ (q x - ⟪q x, x⟫ • x = 0) by
      obtain ⟨x, hx, hx'⟩ := this
      exact ⟨⟨x, hx⟩, hx'⟩
    apply hairy_ball_diff hn odd_n
    refine contDiff_proj (contDiff_euclidean.2 (fun i => ?_))
    exact (p i).contDiff_one.comp
      (ContinuousLinearEquiv.contDiff (EuclideanSpace.equiv (Fin n) ℝ))
    intro x
    rw [inner_sub_left, real_inner_smul_left, inner_self_eq_norm_sq_to_K,
      mem_sphere_zero_iff_norm.1 x.2]
    simp


variable (n)

include hn odd_n continuous_v isTang_v in
theorem hairy_ball : ∃ x, v x = 0 := by
  by_contra!
  let g : C(unitSphere n, ℝ) := ⟨fun x => ‖v x‖⁻¹,
    (continuous_norm.comp continuous_v).inv₀ (fun x => norm_ne_zero_iff.2 (this x))⟩
  have g_pos : 0 < ‖g‖ := by
    have _ : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 odd_n.pos
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty («E» := E n)).2 zero_le_one
    refine norm_pos_iff.2 (fun h => this ⟨x, hx⟩ (norm_eq_zero.1 (inv_eq_zero.1 ?_)))
    show g ⟨x, hx⟩ = 0
    simp [h]
  obtain ⟨v', hv', x, x0⟩ := exists_near_v_vanishing hn odd_n continuous_v isTang_v ‖g‖⁻¹
    (inv_pos.2 g_pos)
  apply (hv' x).not_ge
  rw [x0, zero_sub, norm_neg, inv_le_comm₀ g_pos (norm_pos_iff.2 (this x)),
    ← norm_norm, ← norm_inv]
  exact g.norm_coe_le_norm x


end
