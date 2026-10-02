module

public import Mathlib

/-!
Compact comparison surface for the Cremer-McLean full surplus extraction theorem.
All definitions below are genuine, with their exact library bodies.
Only the three comparator-selected theorem proofs are deliberate statement holes.
The complete, independently reviewed proofs are in CremerMcLean, imported by Solution.
The official comparator checks their exact contracts; dependency auditing and
three-kernel passes check the complete Solution rather than these placeholders.
-/

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
  sorry
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
  sorry
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
  sorry
end

end CremerMcLean
