module

public import Mathlib

/-!
Basic definitions for Cremer-McLean full surplus extraction with finite types,
a correlated prior, and interdependent values.
-/

@[expose] public section

open scoped BigOperators

namespace CremerMcLean

noncomputable section

variable {n : Nat}

/-- A full type profile, specifying a type for every bidder. -/
def Profile (T : Fin n -> Type*) := forall i : Fin n, T i

/-- The types of all bidders other than bidder i. -/
def Others (T : Fin n -> Type*) (i : Fin n) :=
  forall j : { j : Fin n // j ≠ i }, T j

variable {T : Fin n -> Type*}
variable [forall i, Fintype (T i)] [forall i, Nonempty (T i)]

/-- Type profiles form a finite type. -/
instance : Fintype (Profile T) := by
  unfold Profile
  infer_instance

/-- Type profiles are nonempty. -/
instance : Nonempty (Profile T) := by
  unfold Profile
  infer_instance

/-- Other bidders' type profiles form a finite type. -/
instance (i : Fin n) : Fintype (Others T i) := by
  haveI : ∀ j : { j : Fin n // j ≠ i }, Fintype (T (j : Fin n)) :=
    fun j => inferInstance
  unfold Others
  infer_instance

/-- Other bidders' type profiles are nonempty. -/
instance (i : Fin n) : Nonempty (Others T i) := by
  have : ∀ j : { j : Fin n // j ≠ i }, Nonempty (T (j : Fin n)) :=
    fun j => inferInstance
  unfold Others
  infer_instance

local notation "Profile" => Profile T
local notation "Others" => Others T

/-- Assemble a full profile from the own type of bidder i and the other types. -/
def joinTypes (i : Fin n) (a : T i) (s : Others i) : Profile :=
  fun j => if h : j = i then h.symm ▸ a else s ⟨j, h⟩

/-- Restrict a full profile to the types of bidders other than bidder i. -/
def othersOf (i : Fin n) (r : Profile) : Others i := fun j => r j.val

omit [∀ _, Fintype (T _)] [∀ _, Nonempty (T _)] in
theorem joinTypes_self (i : Fin n) (a : T i) (s : Others i) :
    joinTypes i a s i = a := by
  simp [joinTypes]

omit [∀ _, Fintype (T _)] [∀ _, Nonempty (T _)] in
theorem joinTypes_other (i : Fin n) (a : T i) (s : Others i)
    (j : Fin n) (h : j ≠ i) :
    joinTypes i a s j = s ⟨j, h⟩ := by
  simp [joinTypes, h]

omit [∀ _, Fintype (T _)] [∀ _, Nonempty (T _)] in
theorem joinTypes_othersOf (i : Fin n) (r : Profile) :
    joinTypes i (r i) (othersOf i r) = r := by
  funext j
  by_cases h : j = i
  · subst j
    simp [joinTypes]
  · simp [joinTypes, othersOf, h]

/-- The marginal probability of the own type of bidder i. -/
def marginalProb (pi : Profile -> Real) (i : Fin n) (a : T i) : Real :=
  ∑ s : Others i, pi (joinTypes i a s)

/-- The conditional distribution of the other types given the own type. -/
def condDist (pi : Profile -> Real) (i : Fin n) (a : T i) : Others i -> Real :=
  fun s => pi (joinTypes i a s) / marginalProb pi i a

/-- No conditional distribution belongs to the convex hull of the others. -/
def ConvexIndependent (pi : Profile -> Real) : Prop :=
  forall i : Fin n, forall a : T i,
    condDist pi i a ∉ convexHull Real
      { b : Others i -> Real | exists c : T i, c ≠ a ∧ b = condDist pi i c }

/-- Interim expected utility for true type t and reported type r.
    Allocation and payment use the reported profile, while the bidder's
    value is evaluated at the true type profile (interdependent values). -/
def interimUtil (pi : Profile -> Real) (v : forall _ : Fin n, Profile -> Real)
    (q p : forall _ : Fin n, Profile -> Real) (i : Fin n) (t r : T i) : Real :=
  ∑ s : Others i, condDist pi i t s *
    (q i (joinTypes i r s) * v i (joinTypes i t s) - p i (joinTypes i r s))

/-- Truthful reporting maximizes interim expected utility. -/
def IsBIC (pi : Profile -> Real) (v : forall _ : Fin n, Profile -> Real)
    (q p : forall _ : Fin n, Profile -> Real) : Prop :=
  forall i : Fin n, forall t r : T i,
    interimUtil pi v q p i t r <= interimUtil pi v q p i t t

/-- Truthful interim expected utility is nonnegative for every type. -/
def IsInterimIR (pi : Profile -> Real) (v : forall _ : Fin n, Profile -> Real)
    (q p : forall _ : Fin n, Profile -> Real) : Prop :=
  forall i : Fin n, forall t : T i, 0 <= interimUtil pi v q p i t t

omit [∀ _, Fintype (T _)] [∀ _, Nonempty (T _)] in
theorem exists_maximal_value (hn : 0 < n) (v : forall _ : Fin n, Profile -> Real)
    (r : Profile) : exists i : Fin n, forall j : Fin n, v j r <= v i r := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin n)) (fun i => v i r)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  exact ⟨i, fun j => hmax j (Finset.mem_univ j)⟩

/-- A bidder with maximal value at the given profile. -/
noncomputable def winner (v : forall _ : Fin n, Profile -> Real) (hn : 0 < n)
    (r : Profile) : Fin n :=
  Classical.choose (exists_maximal_value hn v r)

omit [∀ _, Fintype (T _)] [∀ _, Nonempty (T _)] in
theorem winner_is_maximal (v : forall _ : Fin n, Profile -> Real) (hn : 0 < n)
    (r : Profile) (j : Fin n) : v j r <= v (winner v hn r) r := by
  exact Classical.choose_spec (exists_maximal_value hn v r) j

/-- Efficient allocation: unit mass on a maximal-value bidder. -/
def cmAlloc (v : forall _ : Fin n, Profile -> Real) (hn : 0 < n) :
    forall _ : Fin n, Profile -> Real :=
  fun i r => if i = winner v hn r then 1 else 0

/-- Payment: full value extraction plus the scaled side bet. -/
def cmPay (v : forall _ : Fin n, Profile -> Real) (hn : 0 < n) (K : Real)
    (c : forall i : Fin n, forall _ : T i, Others i -> Real) : forall _ : Fin n, Profile -> Real :=
  fun i r => cmAlloc v hn i r * v i r + K * c i (r i) (othersOf i r)

/-- The object is allocated with total mass one to maximal-value bidders. -/
def IsEfficient (v : forall _ : Fin n, Profile -> Real) (_hn : 0 < n)
    (q : forall _ : Fin n, Profile -> Real) : Prop :=
  (forall r : Profile, ∑ i : Fin n, q i r = 1) ∧
  (forall r : Profile, forall i : Fin n, q i r ≠ 0 ->
    forall j : Fin n, v j r <= v i r)

/-- Expected seller revenue equals the expected welfare of the allocation. -/
def FullSurplus (pi : Profile -> Real) (v : forall _ : Fin n, Profile -> Real)
    (q p : forall _ : Fin n, Profile -> Real) : Prop :=
  (∑ r : Profile, pi r * ∑ i : Fin n, p i r) =
    (∑ r : Profile, pi r * ∑ i : Fin n, q i r * v i r)

theorem marginalProb_pos (pi : Profile -> Real) (i : Fin n) (a : T i)
    (hpi_pos : forall t, 0 < pi t) : 0 < marginalProb pi i a := by
  classical
  unfold marginalProb
  exact Finset.sum_pos (fun s hs => hpi_pos (joinTypes i a s)) Finset.univ_nonempty

omit [∀ _, Nonempty (T _)] in
theorem condDist_nonneg (pi : Profile -> Real) (i : Fin n) (a : T i)
    (hpi_nonneg : forall t, 0 <= pi t) : forall s, 0 <= condDist pi i a s := by
  intro s
  unfold condDist
  apply div_nonneg (hpi_nonneg (joinTypes i a s))
  exact Finset.sum_nonneg (fun u hu => hpi_nonneg (joinTypes i a u))

theorem condDist_sum (pi : Profile -> Real) (i : Fin n) (a : T i)
    (hpi_pos : forall t, 0 < pi t) : ∑ s : Others i, condDist pi i a s = 1 := by
  unfold condDist
  rw [← Finset.sum_div]
  change marginalProb pi i a / marginalProb pi i a = 1
  exact div_self (ne_of_gt (marginalProb_pos pi i a hpi_pos))

omit [∀ _, Fintype (T _)] [∀ _, Nonempty (T _)] in
theorem cmAlloc_nonneg (v : forall _ : Fin n, Profile -> Real) (hn : 0 < n)
    (i : Fin n) (r : Profile) : 0 <= cmAlloc v hn i r := by
  unfold cmAlloc
  split <;> norm_num

omit [∀ _, Fintype (T _)] [∀ _, Nonempty (T _)] in
theorem cmAlloc_le_one (v : forall _ : Fin n, Profile -> Real) (hn : 0 < n)
    (i : Fin n) (r : Profile) : cmAlloc v hn i r <= 1 := by
  unfold cmAlloc
  split <;> norm_num

omit [∀ _, Fintype (T _)] [∀ _, Nonempty (T _)] in
theorem cmAlloc_sum_one (v : forall _ : Fin n, Profile -> Real) (hn : 0 < n)
    (r : Profile) : ∑ i : Fin n, cmAlloc v hn i r = 1 := by
  classical
  simp [cmAlloc]

theorem separating_lottery
    (pi : Profile -> Real) (hpi_pos : forall t, 0 < pi t)
    (hpi_sum : ∑ t : Profile, pi t = 1)
    (hCI : ConvexIndependent pi) :
    forall i : Fin n, forall s : T i, exists x : Others i -> Real,
      (∑ u : Others i, condDist pi i s u * x u = 0) ∧
      (forall t : T i, t ≠ s -> 0 < ∑ u : Others i, condDist pi i t u * x u) := by
  classical
  have _ := hpi_sum
  intro i s
  by_cases h : ∃ t : T i, t ≠ s
  · let E := PiLp 2 (fun _ : Others i => ℝ)
    let φ : (Others i → ℝ) ≃ₗ[ℝ] E :=
      (WithLp.linearEquiv 2 ℝ (Others i → ℝ)).symm
    let S : Set (Others i → ℝ) :=
      {b | ∃ c : T i, c ≠ s ∧ b = condDist pi i c}
    let K : Set E := convexHull ℝ (φ '' S)
    have hS : S.Finite := by
      have hS_eq : S = (fun c => condDist pi i c) '' {c : T i | c ≠ s} := by
        ext b
        constructor
        · rintro ⟨c, hc, rfl⟩
          exact ⟨c, hc, rfl⟩
        · rintro ⟨c, hc, rfl⟩
          exact ⟨c, hc, rfl⟩
      rw [hS_eq]
      exact (Set.toFinite _).image _
    have hK_closed : IsClosed K := (hS.image φ).isClosed_convexHull ℝ
    have hK_convex : Convex ℝ K := convex_convexHull ℝ _
    have houtside : φ (condDist pi i s) ∉ K := by
      intro hmem
      change φ (condDist pi i s) ∈ convexHull ℝ (φ.toLinearMap '' S) at hmem
      rw [← LinearMap.image_convexHull φ.toLinearMap S] at hmem
      obtain ⟨b, hb, hbb⟩ := hmem
      have hb_eq : b = condDist pi i s := φ.injective hbb
      subst b
      exact hCI i s hb
    obtain ⟨g, a, hg, ha⟩ :=
      geometric_hahn_banach_point_closed hK_convex hK_closed houtside
    let f : StrongDual ℝ E := -g
    let u : ℝ := -a
    have hf (b : E) (hb : b ∈ K) : f b < u := neg_lt_neg (ha b hb)
    have hu : u < f (φ (condDist pi i s)) := neg_lt_neg hg
    let w : Others i → ℝ := fun v => f (φ (Pi.single v 1))
    have key (y : Others i → ℝ) : f (φ y) = ∑ v, w v * y v := by
      conv_lhs => rw [pi_eq_sum_univ' y]
      simp only [map_sum, map_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro v _
      exact mul_comm _ _
    let x : Others i → ℝ := fun v => f (φ (condDist pi i s)) - w v
    have expected (t : T i) :
        ∑ v, condDist pi i t v * x v =
          f (φ (condDist pi i s)) - f (φ (condDist pi i t)) := by
      calc
        ∑ v, condDist pi i t v * x v =
            (∑ v, condDist pi i t v) * f (φ (condDist pi i s)) -
              ∑ v, w v * condDist pi i t v := by
          simp only [x, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro v _
          exact mul_comm _ _
        _ = f (φ (condDist pi i s)) - f (φ (condDist pi i t)) := by
          rw [condDist_sum pi i t hpi_pos, one_mul, ← key]
    refine ⟨x, ?_, ?_⟩
    · rw [expected, sub_self]
    · intro t ht
      have ht_mem : φ (condDist pi i t) ∈ K :=
        subset_convexHull ℝ (φ '' S) ⟨condDist pi i t, ⟨t, ht, rfl⟩, rfl⟩
      rw [expected]
      exact sub_pos.mpr (lt_trans (hf _ ht_mem) hu)
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · simp
    · intro t ht
      exact (h ⟨t, ht⟩).elim

theorem bic_of_good_lotteries
    (pi : Profile -> Real) (hpi_pos : forall t, 0 < pi t)
    (hpi_sum : ∑ t : Profile, pi t = 1)
    (v : forall _ : Fin n, Profile -> Real) (hv : forall i t, 0 <= v i t)
    (hn : 0 < n)
    (c : forall i : Fin n, forall _ : T i, Others i -> Real)
    (delta : Real) (hdelta : 0 < delta)
    (V : Real) (hV : 0 <= V)
    (hVbound : forall i : Fin n, forall t r : T i, forall s : Others i,
      abs (v i (joinTypes i t s) - v i (joinTypes i r s)) <= V)
    (hLot0 : forall i : Fin n, forall s : T i,
      ∑ u : Others i, condDist pi i s u * c i s u = 0)
    (hLotPos : forall i : Fin n, forall s t : T i, t ≠ s ->
      delta <= ∑ u : Others i, condDist pi i t u * c i s u)
    (K : Real) (hK : V / delta + 1 <= K) :
    IsBIC pi v (cmAlloc v hn) (cmPay v hn K c) ∧
    (forall i : Fin n, forall t : T i,
      interimUtil pi v (cmAlloc v hn) (cmPay v hn K c) i t t = 0) := by
  classical
  have _ := hpi_sum
  have _ := hv
  have othersOf_join (i : Fin n) (r : T i) (s : Others i) :
      othersOf i (joinTypes i r s) = s := by
    funext j
    exact joinTypes_other i r s j.val j.property
  let A (i : Fin n) (t r : T i) : Real :=
    ∑ s : Others i, condDist pi i t s *
      (cmAlloc v hn i (joinTypes i r s) *
        (v i (joinTypes i t s) - v i (joinTypes i r s)))
  let E (i : Fin n) (t r : T i) : Real :=
    ∑ s : Others i, condDist pi i t s * c i r s
  have utility (i : Fin n) (t r : T i) :
      interimUtil pi v (cmAlloc v hn) (cmPay v hn K c) i t r =
        A i t r - K * E i t r := by
    calc
      interimUtil pi v (cmAlloc v hn) (cmPay v hn K c) i t r =
          ∑ s : Others i,
            (condDist pi i t s *
              (cmAlloc v hn i (joinTypes i r s) *
                (v i (joinTypes i t s) - v i (joinTypes i r s))) -
              K * (condDist pi i t s * c i r s)) := by
        unfold interimUtil cmPay
        apply Finset.sum_congr rfl
        intro s _
        rw [joinTypes_self, othersOf_join]
        ring
      _ = A i t r - K * E i t r := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have truthful (i : Fin n) (t : T i) :
      interimUtil pi v (cmAlloc v hn) (cmPay v hn K c) i t t = 0 := by
    rw [utility]
    simp only [A, sub_self, mul_zero, Finset.sum_const_zero, E, hLot0]
  have gain_le (i : Fin n) (t r : T i) : A i t r ≤ V := by
    calc
      A i t r ≤ ∑ s : Others i, condDist pi i t s * V := by
        apply Finset.sum_le_sum
        intro s _
        have hd : v i (joinTypes i t s) - v i (joinTypes i r s) ≤ V :=
          (le_abs_self _).trans (hVbound i t r s)
        have hq : cmAlloc v hn i (joinTypes i r s) *
            (v i (joinTypes i t s) - v i (joinTypes i r s)) ≤ V := by
          calc
            _ ≤ cmAlloc v hn i (joinTypes i r s) * V :=
              mul_le_mul_of_nonneg_left hd (cmAlloc_nonneg v hn i _)
            _ ≤ 1 * V :=
              mul_le_mul_of_nonneg_right (cmAlloc_le_one v hn i _) hV
            _ = V := one_mul V
        exact mul_le_mul_of_nonneg_left hq
          (condDist_nonneg pi i t (fun u => (hpi_pos u).le) s)
      _ = V := by
        rw [← Finset.sum_mul, condDist_sum pi i t hpi_pos, one_mul]
  have hKbound : V / delta ≤ K := by linarith
  have hKnonneg : 0 ≤ K := (div_nonneg hV hdelta.le).trans hKbound
  have payment_ge (i : Fin n) (t r : T i) (h : t ≠ r) : V ≤ K * E i t r := by
    have hE : delta ≤ E i t r := hLotPos i r t h
    exact ((div_le_iff₀ hdelta).mp hKbound).trans
      (mul_le_mul_of_nonneg_left hE hKnonneg)
  refine ⟨?_, truthful⟩
  intro i t r
  by_cases h : t = r
  · subst r
    exact le_rfl
  · rw [utility, truthful]
    exact sub_nonpos.mpr ((gain_le i t r).trans (payment_ge i t r h))

theorem full_extraction
    (pi : Profile -> Real) (hpi_pos : forall t, 0 < pi t)
    (hpi_sum : ∑ t : Profile, pi t = 1)
    (v : forall _ : Fin n, Profile -> Real) (hv : forall i t, 0 <= v i t)
    (hn : 0 < n)
    (hCI : ConvexIndependent pi) :
    exists K : Real, exists c : forall i : Fin n, forall _ : T i, Others i -> Real,
      IsEfficient v hn (cmAlloc v hn) ∧
      IsBIC pi v (cmAlloc v hn) (cmPay v hn K c) ∧
      IsInterimIR pi v (cmAlloc v hn) (cmPay v hn K c) ∧
      FullSurplus pi v (cmAlloc v hn) (cmPay v hn K c) := by
  classical
  choose x hx0 hxpos using separating_lottery pi hpi_pos hpi_sum hCI
  have othersOf_join (i : Fin n) (r : T i) (s : Others i) :
      othersOf i (joinTypes i r s) = s := by
    funext j
    exact joinTypes_other i r s j.val j.property
  let V : ℝ := ∑ i : Fin n, ∑ t : T i, ∑ r : T i, ∑ s : Others i,
    |v i (joinTypes i t s) - v i (joinTypes i r s)|
  have hV : 0 ≤ V := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun t _ =>
      Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun s _ => abs_nonneg _
  have hVbound (i : Fin n) (t r : T i) (s : Others i) :
      |v i (joinTypes i t s) - v i (joinTypes i r s)| ≤ V := by
    calc
      _ ≤ ∑ u : Others i, |v i (joinTypes i t u) - v i (joinTypes i r u)| :=
        Finset.single_le_sum
          (f := fun u : Others i => |v i (joinTypes i t u) - v i (joinTypes i r u)|)
          (fun u _ => abs_nonneg _) (Finset.mem_univ s)
      _ ≤ ∑ a : T i, ∑ u : Others i,
          |v i (joinTypes i t u) - v i (joinTypes i a u)| :=
        Finset.single_le_sum
          (f := fun a : T i => ∑ u : Others i,
            |v i (joinTypes i t u) - v i (joinTypes i a u)|)
          (fun a _ => Finset.sum_nonneg fun u _ => abs_nonneg _) (Finset.mem_univ r)
      _ ≤ ∑ b : T i, ∑ a : T i, ∑ u : Others i,
          |v i (joinTypes i b u) - v i (joinTypes i a u)| :=
        Finset.single_le_sum
          (f := fun b : T i => ∑ a : T i, ∑ u : Others i,
            |v i (joinTypes i b u) - v i (joinTypes i a u)|)
          (fun b _ => Finset.sum_nonneg fun a _ =>
            Finset.sum_nonneg fun u _ => abs_nonneg _) (Finset.mem_univ t)
      _ ≤ V := by
        apply Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin n => ∑ b : T j, ∑ a : T j, ∑ u : Others j,
            |v j (joinTypes j b u) - v j (joinTypes j a u)|)
        · intro j _
          exact Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun a _ =>
            Finset.sum_nonneg fun u _ => abs_nonneg _
        · exact Finset.mem_univ i
  let idx : Finset (Σ i : Fin n, T i × T i) := Finset.univ
  let val : (Σ i : Fin n, T i × T i) → ℝ := fun p =>
    if p.2.2 ≠ p.2.1 then
      ∑ u : Others p.1, condDist pi p.1 p.2.2 u * x p.1 p.2.1 u
    else 1
  have hidx : idx.Nonempty := by
    let i₀ : Fin n := ⟨0, hn⟩
    obtain ⟨t₀⟩ := (inferInstance : Nonempty (T i₀))
    exact ⟨⟨i₀, (t₀, t₀)⟩, Finset.mem_univ _⟩
  let delta : ℝ := (idx.image val).min' (hidx.image val)
  have hdelta : 0 < delta := by
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp (Finset.min'_mem _ (hidx.image val))
    change val p = delta at hp
    rw [← hp]
    dsimp only [val]
    split
    · exact hxpos p.1 p.2.1 p.2.2 ‹p.2.2 ≠ p.2.1›
    · exact one_pos
  have hLotPos (i : Fin n) (s t : T i) (h : t ≠ s) :
      delta ≤ ∑ u : Others i, condDist pi i t u * x i s u := by
    have hle : delta ≤ val ⟨i, (s, t)⟩ :=
      Finset.min'_le (idx.image val) (val ⟨i, (s, t)⟩)
        (Finset.mem_image.mpr ⟨⟨i, (s, t)⟩, Finset.mem_univ _, rfl⟩)
    simpa only [val, ite_eq_left h] using hle
  let K : ℝ := V / delta + 1
  have hK : V / delta + 1 ≤ K := le_rfl
  obtain ⟨hbic, htruth⟩ := bic_of_good_lotteries pi hpi_pos hpi_sum v hv hn
    x delta hdelta V hV hVbound hx0 hLotPos K hK
  have efficient : IsEfficient v hn (cmAlloc v hn) := by
    refine ⟨cmAlloc_sum_one v hn, ?_⟩
    intro r i hne j
    have hi : i = winner v hn r := by
      by_contra h
      simp [cmAlloc, h] at hne
    rw [hi]
    exact winner_is_maximal v hn r j
  have ir : IsInterimIR pi v (cmAlloc v hn) (cmPay v hn K x) := by
    intro i t
    rw [htruth i t]
  have key (i : Fin n) : ∑ r : Profile, pi r * x i (r i) (othersOf i r) = 0 := by
    let e : T i × Others i ≃ Profile :=
      { toFun := fun p => joinTypes i p.1 p.2
        invFun := fun r => (r i, othersOf i r)
        left_inv := by
          rintro ⟨t, s⟩
          dsimp only
          rw [joinTypes_self, othersOf_join]
        right_inv := joinTypes_othersOf i }
    calc
      _ = ∑ p : T i × Others i,
          pi (joinTypes i p.1 p.2) * x i p.1 p.2 := by
        rw [← Equiv.sum_comp e (fun r => pi r * x i (r i) (othersOf i r))]
        apply Finset.sum_congr rfl
        intro p _
        change pi (joinTypes i p.1 p.2) *
          x i (joinTypes i p.1 p.2 i) (othersOf i (joinTypes i p.1 p.2)) = _
        rw [joinTypes_self, othersOf_join]
      _ = ∑ t : T i, ∑ s : Others i, pi (joinTypes i t s) * x i t s :=
        Fintype.sum_prod_type _
      _ = ∑ t : T i, marginalProb pi i t *
          ∑ s : Others i, condDist pi i t s * x i t s := by
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        have hp : pi (joinTypes i t s) = condDist pi i t s * marginalProb pi i t :=
          (div_mul_cancel₀ _ (ne_of_gt (marginalProb_pos pi i t hpi_pos))).symm
        rw [hp]
        ring
      _ = 0 := by simp only [hx0, mul_zero, Finset.sum_const_zero]
  have surplus : FullSurplus pi v (cmAlloc v hn) (cmPay v hn K x) := by
    unfold FullSurplus
    calc
      _ = (∑ r : Profile, pi r * ∑ i : Fin n, cmAlloc v hn i r * v i r) +
          K * ∑ i : Fin n, ∑ r : Profile, pi r * x i (r i) (othersOf i r) := by
        simp only [cmPay, Finset.sum_add_distrib, Finset.mul_sum, mul_add]
        rw [Finset.sum_comm (f := fun r i => pi r * (K * x i (r i) (othersOf i r)))]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ = _ := by simp only [key, Finset.sum_const_zero, mul_zero, add_zero]
  exact ⟨K, x, efficient, hbic, ir, surplus⟩

end

end CremerMcLean
