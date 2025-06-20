import Mathlib
-- import Lean.Data.RBMap
-- import Std.Collections
import LeanExperiments.PatchedCollectAxioms
open Batteries

section Def

variable {σ R : Type*} [Semiring R]
#print Nat.eq_or_lt_of_le
inductive TreeRepr (σ : Type*) (R : Type*) where
  | const : R → TreeRepr σ R
  | var : σ → TreeRepr σ R
  | add : TreeRepr σ R → TreeRepr σ R → TreeRepr σ R
  | mul : TreeRepr σ R → TreeRepr σ R → TreeRepr σ R
  | pow : TreeRepr σ R → ℕ → TreeRepr σ R
  | ref : TreeRepr σ R → TreeRepr σ R
with
  @[computed_field, semireducible]
  totalDegreeBound : ∀ (σ) (R), TreeRepr σ R → ℕ
    | _, _, .const _ => 0
    | _, _, .var _ => 1
    | _, _, .add p q => max p.totalDegreeBound q.totalDegreeBound
    | _, _, .mul p q => max p.totalDegreeBound q.totalDegreeBound
    | _, _, .pow p n => p.totalDegreeBound * n
    | _, _, .ref p => p.totalDegreeBound

  -- @[computed_field]
  -- powDepth_ : ∀ (σ) (R), TreeRepr σ R → ℕ
  -- | _, _, .const _ => 0
  -- | _, _, .var _ => 0
  -- | _, _, .add p q => 0 --max p.powDepth_ q.powDepth_
  -- | _, _, .mul p q => 0 --max p.powDepth_ q.powDepth_
  -- | _, _, .pow p n => 0 --n + p.powDepth_
  -- | _, _, .ref p => 0 --p.powDepth_
deriving Repr

def TreeRepr.eval (p : TreeRepr σ R) (f : σ → R) : R :=
  match p with
  | const c => c
  | var v => f v
  | add p q => p.eval f + q.eval f
  | mul p q => p.eval f * q.eval f
  | pow p n => (p.eval f) ^ n
  | ref p => p.eval f

#print TreeRepr.brecOn

#print TreeRepr.rec

#print TreeRepr.eval

-- def TreeRepr.toExpandedRBTree
-- mutual

--   def TreeRepr.toExpandedRBTreePow (i_ord : σ → σ → Ordering)
--     (ord : RBMap σ ℕ i_ord → RBMap σ ℕ i_ord → Ordering)
--     (p : TreeRepr σ R) : ℕ → RBMap (RBMap σ ℕ i_ord) R ord
--       | 0 => RBMap.fromArray #[(RBMap.empty, 1)] _
--       | 1 => p.toExpandedRBTree' _ _
--       | .succ (.succ n) =>
--         letI := (TreeRepr.pow p (n / 2)).toExpandedRBTree' i_ord ord
--         sorry

def TreeRepr._RBMapAdd [∀ (c : R), Decidable (c = 0)] (i_ord : σ → σ → Ordering)
    (ord : RBMap σ ℕ i_ord → RBMap σ ℕ i_ord → Ordering)
    (p q : RBMap (RBMap σ ℕ i_ord) R ord) : RBMap (RBMap σ ℕ i_ord) R ord :=
  p.mergeWith (fun _ => HAdd.hAdd) q

def TreeRepr._RBMapMul [∀ (c : R), Decidable (c = 0)] (i_ord : σ → σ → Ordering)
    (ord : RBMap σ ℕ i_ord → RBMap σ ℕ i_ord → Ordering)
    (p q : RBMap (RBMap σ ℕ i_ord) R ord) : RBMap (RBMap σ ℕ i_ord) R ord :=
  p.foldl (fun a e c ↦ TreeRepr._RBMapAdd _ _
      a
      (q.map <| fun ⟨e', c'⟩ => ⟨e'.mergeWith (fun _ ↦ Nat.add) e, c' * c⟩))
    .empty

def TreeRepr._RBMapPow [∀ (c : R), Decidable (c = 0)] (i_ord : σ → σ → Ordering)
    (ord : RBMap σ ℕ i_ord → RBMap σ ℕ i_ord → Ordering)
    (p : RBMap (RBMap σ ℕ i_ord) R ord) : (n : ℕ) → RBMap (RBMap σ ℕ i_ord) R ord
| 0 => RBMap.single RBMap.empty 1
| 1 => p
| .succ m =>
  TreeRepr._RBMapMul _ _ (TreeRepr._RBMapPow _ _ p m) p

def TreeRepr._RBMapPow' [∀ (c : R), Decidable (c = 0)] (i_ord : σ → σ → Ordering)
    (ord : RBMap σ ℕ i_ord → RBMap σ ℕ i_ord → Ordering)
    (p : RBMap (RBMap σ ℕ i_ord) R ord) : (fuel : ℕ) → (n : ℕ) → RBMap (RBMap σ ℕ i_ord) R ord
| _, 0 => RBMap.single RBMap.empty 1
| _, 1 => p
| .succ fuel', m =>
  letI := TreeRepr._RBMapPow' i_ord ord p fuel' (m / 2)
  if m % 2 = 0 then
    this
  else
    TreeRepr._RBMapMul _ _ this p
| _, _ => unreachable!

#print TreeRepr._RBMapPow'

def TreeRepr.toExpandedRBTree [∀ (c : R), Decidable (c = 0)] (i_ord : σ → σ → Ordering)
    (ord : RBMap σ ℕ i_ord → RBMap σ ℕ i_ord → Ordering) :
    (p : TreeRepr σ R) → RBMap (RBMap σ ℕ i_ord) R ord
  | const c => RBMap.single RBMap.empty c
  | var v => RBMap.single (RBMap.single v 1) 1
  | add p q => TreeRepr._RBMapAdd _ _ (p.toExpandedRBTree _ _ ) (q.toExpandedRBTree _ _)
  | mul p q => TreeRepr._RBMapMul _ _ (p.toExpandedRBTree _ _) (q.toExpandedRBTree _ _)
  | pow p n =>
    if n = 0 then
      RBMap.single RBMap.empty 1
    else
      TreeRepr._RBMapPow' _ _ (p.toExpandedRBTree _ _) n n
  | ref p => p.toExpandedRBTree _ _

#print TreeRepr.toExpandedRBTree
-- #check Nat.rem

-- def TreeRepr.toBTreeMap

end Def

open DirectSum

section Polynomial
open Polynomial

variable {σ R : Type*} [Semiring R] (p q : Polynomial R)

def TreeRepr.toDirectSum' : TreeRepr σ R → (⨁ _ : ℕ, R)
  | const c => .single 0 c
  | var _ => .single 1 1
  | add p q => p.toDirectSum' + q.toDirectSum'
  | mul p q => p.toDirectSum' * q.toDirectSum'
  | pow p n => p.toDirectSum' ^ n
  | ref p => p.toDirectSum'

noncomputable def TreeRepr.toPolynomial (t : TreeRepr σ R) : Polynomial R :=
  match t with
  | const c => .C c
  | var _ => .X
  | add p q => p.toPolynomial + q.toPolynomial
  | mul p q => p.toPolynomial * q.toPolynomial
  | pow p n => p.toPolynomial ^ n
  | ref p => p.toPolynomial

lemma TreeRepr.toDirectSum'_eq_toPolynomial_toDirectSum (p : TreeRepr σ R) :
    p.toDirectSum' = p.toPolynomial.toFinsupp.toDirectSum := by
  unfold TreeRepr.toDirectSum' TreeRepr.toPolynomial
  cases p with
  | const c =>
    simp
    rfl
  | var _ =>
    simp
    rfl
  | add p q =>
    simp [toDirectSum'_eq_toPolynomial_toDirectSum]
  | mul p q =>
    simp [toDirectSum'_eq_toPolynomial_toDirectSum]
  | pow p n =>
    simp [toDirectSum'_eq_toPolynomial_toDirectSum]
  | ref p =>
    simp [toDirectSum'_eq_toPolynomial_toDirectSum]

-- lemma TreeRepr.eval
class Polynomial.PolyRepr (p : Polynomial R) where
  tree : TreeRepr Unit R
  tree_eq : tree.toPolynomial = p

def Polynomial.toRepr [p_repr : p.PolyRepr] := p_repr

-- we can make use of it for `DecidableEq (MvPolynomial σ R)` before we find a more efficient way
lemma TreeRepr.polynomial_eq_iff_directSum'_eq [DecidableEq σ]
    [∀ m : R, Decidable (m ≠ 0)]
    (p q : TreeRepr σ R) :
    p.toPolynomial = q.toPolynomial ↔ p.toDirectSum' = q.toDirectSum' := by
  rw [toDirectSum'_eq_toPolynomial_toDirectSum, toDirectSum'_eq_toPolynomial_toDirectSum,
      ← Polynomial.toFinsupp_inj]
  refine Iff.symm (Function.Injective.eq_iff ?_)
  exact addMonoidAlgebraEquivDirectSum.injective

-- lemma PolyRepr.toDirectSum_eq_reeRepr_

lemma PolyRepr.eq_iff_directSum'_eq [p_repr : p.PolyRepr] [q_repr : q.PolyRepr]
    [∀ m : R, Decidable (m ≠ 0)] :
    p = q ↔ p.toRepr.tree.toDirectSum' = q.toRepr.tree.toDirectSum' := by
  nth_rw 1 [← p.toRepr.tree_eq, ← q.toRepr.tree_eq]
  exact TreeRepr.polynomial_eq_iff_directSum'_eq _ _

-- def RBSet.mergeWithFilter {α cmp} (mergeFn : α → α → Option α) (t₁ t₂ : RBSet α cmp) : RBSet α cmp :=
--   t₂.foldl (init := t₁) fun t₁ a₂ =>
--     match t₁.find? a₂ with
--     | some a₁ =>
--       match mergeFn a₁ a₂ with
--       | some a => t₁.insert a
--       | none => t₁.erase (cmp a₂ ·)
--     | none => t₁.insert a₂

-- def RBMap.mergeWithFilter {α β cmp} (mergeFn : α → β → β → Option β) (t₁ t₂ : RBMap α β cmp) : RBMap α β cmp :=
--   RBSet.mergeWithFilter (fun (_, b₁) (a, b₂) => (mergeFn a b₁ b₂).map (a, ·)) t₁ t₂

def TreeRepr._RBMapAdd' [∀ c : R, Decidable (c = 0)]
    (p q : RBMap ℕ R compare) : RBMap ℕ R compare :=
  (RBMap.mergeWith (fun _ a b => a + b) p q).filter (fun _ c ↦ c ≠ 0)
  -- RBMap.mergeWithFilter (fun _ a b => let c := a + b; if c = 0 then none else some c) p q

def TreeRepr._RBMapMul' [∀ c : R, Decidable (c = 0)] (p q : RBMap ℕ R compare) : RBMap ℕ R compare :=
  p.foldl (init := .empty) <|
    fun a e c ↦ TreeRepr._RBMapAdd' a <|
      q.foldl (init := .empty) <|
        fun a' e' c' ↦ let c'' := c * c' ; if c'' = 0 then a' else a'.insert (e + e') c''

-- def TreeRepr._RBMapPow'' [∀ c : R, Decidable (c = 0)]
--     (p : RBMap ℕ R compare) : (fuel : ℕ) → (n : ℕ) → RBMap ℕ R compare
-- | _, 0 => RBMap.single 0 1
-- | _, 1 => p
-- | .succ fuel', m =>
--   let this := TreeRepr._RBMapPow' p fuel' (m / 2)
--   let this := TreeRepr._RBMapMul' this this
--   if m % 2 = 0 then
--     this
--   else
--     TreeRepr._RBMapMul' this p
-- | _, _ => unreachable!

def TreeRepr._RBMapPow'' [∀ c : R, Decidable (c = 0)]
    (p : RBMap ℕ R compare) : ℕ → RBMap ℕ R compare
| 0 => RBMap.single 0 1
| 1 => p
| .succ m =>
  TreeRepr._RBMapMul' (TreeRepr._RBMapPow'' p m) p

-- #print TreeRepr._RBMapPow

def TreeRepr.toExpandedRBTree' [∀ (c : R), Decidable (c = 0)] :
    (p : TreeRepr σ R) → RBMap ℕ R compare
  | const c => if c = 0 then RBMap.empty else RBMap.single 0 c
  | var _ => if (1 : R) = 0 then RBMap.empty else RBMap.single 1 1
  | add p q => TreeRepr._RBMapAdd' p.toExpandedRBTree' q.toExpandedRBTree'
  | mul p q => TreeRepr._RBMapMul' p.toExpandedRBTree' q.toExpandedRBTree'
  | pow p n =>
    TreeRepr._RBMapPow'' p.toExpandedRBTree' n
  | ref p => p.toExpandedRBTree'

-- #check Sigma.

section lemmas

open scoped Classical

section toBarries
-- theorem
end toBarries

theorem TreeRepr.toExpendedRBTree'_no_zero (p : TreeRepr σ R) :
    ∀ a ∈ p.toExpandedRBTree'.toList, a.2 ≠ 0 := by
  unfold TreeRepr.toExpandedRBTree'
  intro a
  cases p with
  | const c => by_cases h : c = 0 <;> simp_intro .. [h]
  | var _ => by_cases h : (1 : R) = 0 <;> simp_intro .. [h]
  | add p q =>
    simp_intro ha [_RBMapAdd', RBMap.mem_toList]
    -- rw [RBSet.mem_iff_find?] at h
    -- convert_to (_ : RBNode (ℕ × R)).MemP _ _ at ha
    -- rw [RBNode.any_] at ha
    -- rw [RBMap.mergeWith]
    sorry
  | mul p q => sorry
  | pow p n => sorry
  | ref p => exact p.toExpendedRBTree'_no_zero a
    -- simp [_RBMapAdd', RBMap.mem_toList]

-- def filter (t : RBSet α cmp) (p : α → Bool) : RBSet α cmp :=
--   t.foldl (init := ∅) fun acc a => bif p a then acc.insert a else acc

lemma Batteries.RBSet.isEmpty_iff_eq_empty {α cmp} (t : RBSet α cmp) :
    t.isEmpty ↔ t = ∅ := by
  match t with
  | ⟨.nil, _⟩ => simp [RBSet.isEmpty]; rfl
  | ⟨.node .., _⟩ =>
    simp [RBSet.isEmpty]
    apply Subtype.mk_eq_mk.not.mpr
    simp

@[simp]
lemma Batteries.RBSet.empty_filter {α cmp} (p : α → Bool) : (∅ : RBSet α cmp).filter p = ∅ := rfl

#check RBSet.toList_sorted

lemma Batteries.RBSet.filter_toList_eq_toList_filter {α cmp} (t : RBSet α cmp) (p : α → Bool) :
    (t.filter p).toList = t.toList.filter p := by
  sorry

theorem baz : ((X + 1 : (ZMod 11)[X]) ^ 11) ^ 11 = X ^ 121 + 1 := by
  grind
#print baz
#print baz._proof_1_1
#print axioms baz
--   match t with
--   | ⟨.nil, wf⟩ => rfl
--   | ⟨.node .., wf⟩ =>

-- #check RBMap.filter
lemma Batteries.RBMap.filter_toList_eq_toList_filter {α β cmp} (t : RBMap α β cmp)
    (p : α → β → Bool) : (t.filter p).toList = t.toList.filter fun ⟨a, b⟩ ↦ p a b :=
  Batteries.RBSet.filter_toList_eq_toList_filter ..

  -- rw [List.]

--   cases h : t.toList with
--   | nil =>
--     simp
--     rw [← RBSet.isEmpty_iff_toList_eq_nil, RBSet.isEmpty_iff_eq_empty] at h
--     rw [h, RBSet.empty_filter, RBSet.empty_toList]
--   | cons a t' =>
--     -- ext i b
--     -- rw [RBSet]
--     rw [RBSet.filter_toList_eq_toList_filter, h]
-- termination_by t.toList.length
-- decreasing_by
--   sorry


    -- rw [RBSet.empty_eq]
    -- unfold RBSet.isEmpty at h
    -- have : t.1 = RBNode.nil := sorry
    -- rw [RBSet.empty_eq]
  -- decide +revert
  --   rw []
  -- rw [List.filter_eq_foldr, RBSet.foldl_eq_foldl_toList]

  -- sorry

-- #check Ordering.swap

lemma Batteries.RBSet.mem_filter {α cmp} (t : RBSet α cmp) (p : α → Bool) (a : α)
    (h : ∀ a', cmp a a' = .eq → p a = p a') :
    a ∈ t.filter p ↔ a ∈ t ∧ p a == True := by
  simp [RBSet.mem_iff_mem_toList, RBSet.filter_toList_eq_toList_filter]
  constructor
  · rintro ⟨a', ⟨ha', ha'2⟩ , ha'3⟩
    constructor
    · use a'
    · rwa [h _ ha'3]
  · rintro ⟨⟨a', ha', ha'1⟩, ha'2⟩
    use a'
    simp [ha', ha'2, ha'1]
    rwa [← h _ ha'1]

-- lemma Batteries.RBMap.mem_filter {α β cmp} (t : RBMap α β cmp)
--     (p : α → β → Bool) (ab : α × β) : ab ∈ t.filter p ↔ a ∈ t ∧ p a == True :=
--   Batteries.RBSet.filter_toList_eq_toList_filter ..
-- #check RBMap.rb

theorem TreeRepr.toExpendedRBTree'_coeff (p : TreeRepr σ R) (n : ℕ) (hn : n ∈ p.toPolynomial.support) :
    RBSet.instMembership.mem p.toExpandedRBTree' (n, p.toPolynomial.coeff n) := by
  -- have : p.toPolynomial.coeff n ≠ 0 := by sorry
  unfold TreeRepr.toExpandedRBTree' TreeRepr.toPolynomial at *
  cases p with
  | const c =>
    simp at *
    simp [Polynomial.coeff_C] at hn
    simp [hn, RBSet.mem_iff_mem_toList, RBMap.single, RBSet.single_toList]
    rfl
  | var _ =>
    simp at *
    simp [Polynomial.coeff_X] at hn
    have : (1 : R) ≠ 0 := sorry
    simp [this, hn.1.symm, hn.2, RBSet.mem_iff_mem_toList, RBMap.single, RBSet.single_toList]
    rfl
  | add p q =>
    simp at *
    simp [_RBMapAdd']
    apply (Batteries.RBSet.mem_filter _ _ _ _).mpr
    ·
      simp [RBMap.mergeWith]
      -- rw [RBSet.mem_merg]
      sorry
    ·
      sorry
    -- simp [hn]
    -- rw [RBSet.mem_iff_mem_toList]
    -- simp
    -- simp [RBSet.mem_filter_iff]
    -- rw [RBMap.filter_toList_eq_toList_filter]
  | mul p q =>
    sorry
  | pow p q =>
    sorry
  | ref p => exact TreeRepr.toExpendedRBTree'_coeff p n hn



theorem TreeRepr.toExpendedRBTree'_eq_coeff (p : TreeRepr σ R) (n : ℕ) :
    (p.toExpandedRBTree'.find? n).getD 0 = p.toPolynomial.coeff n := by
  unfold TreeRepr.toExpandedRBTree' TreeRepr.toPolynomial
  cases p with
  | const c =>
    by_cases h : c = 0
    · simp [h]
      rfl
    · simp [h]
      by_cases hn : n = 0
      · simp [hn]
        rfl
      · rw [Polynomial.coeff_C_ne_zero hn]
        -- unfold RBMap.single RBMap.find? RBMap.findEntry?
        simp [Option.getD_eq_iff]
        right
        unfold RBMap.single RBMap.find? RBMap.findEntry?
        convert Option.map_none Prod.snd
        rw [Option.eq_none_iff_forall_ne_some]
        rw [← not_exists]
        -- rw [← RBSet.]
        -- rw [← RBSet.not_mem]
        sorry
        -- rw [RBMap.find?_some_mem_toList]
  | var _ => sorry
  | add p q =>
    -- simp_intro ha [_RBMapAdd', RBMap.mem_toList]
    -- convert_to (_ : RBNode (ℕ × R)).MemP _ _ at ha
    -- rw [RBNode.any_] at ha
    -- rw [RBMap.mergeWith]
    sorry
  | mul p q => sorry
  | pow p n => sorry
  | ref p => exact p.toExpendedRBTree'_eq_coeff n

theorem TreeRepr.toExpendedRBTree'_eq (p : TreeRepr σ R) :
    p.toExpandedRBTree' ==
    RBMap.ofList p.toPolynomial.toFinsupp.graph.toList _ := by
  cases p with
  | const c => sorry
  | var _ => sorry
  | add p q => sorry
  | mul p q => sorry
  | pow p m => sorry
  | ref p => sorry

end lemmas

theorem PolyRepr.eq_of_toExpandedRBTree'_eq [p_repr : p.PolyRepr] [q_repr : q.PolyRepr]
    [DecidableEq R] (h : p.toRepr.tree.toExpandedRBTree' == q.toRepr.tree.toExpandedRBTree') :
    p = q := by
  nth_rw 1 [← p.toRepr.tree_eq, ← q.toRepr.tree_eq]
  sorry

-- theorem

theorem PolyRepr.eq_iff_toExpandedRBTree'_eq [p_repr : p.PolyRepr] [q_repr : q.PolyRepr]
    [DecidableEq R] :
    p = q ↔ (p.toRepr.tree.toExpandedRBTree' == q.toRepr.tree.toExpandedRBTree') := by
  nth_rw 1 [← p.toRepr.tree_eq, ← q.toRepr.tree_eq]
  sorry

namespace Polynomial

instance {c} : (C c : Polynomial R).PolyRepr where
  tree := .const c
  tree_eq := rfl

instance : (X : Polynomial R).PolyRepr where
  tree := .var 0
  tree_eq := rfl

instance [p.PolyRepr] [q.PolyRepr] : (p * q).PolyRepr where
  tree := .mul p.toRepr.tree q.toRepr.tree
  tree_eq := by
    rw [TreeRepr.toPolynomial, p.toRepr.tree_eq, q.toRepr.tree_eq]

instance [p.PolyRepr] [q.PolyRepr] : (p + q).PolyRepr where
  tree := .add p.toRepr.tree q.toRepr.tree
  tree_eq := by
    rw [TreeRepr.toPolynomial, p.toRepr.tree_eq, q.toRepr.tree_eq]

instance [p.PolyRepr] {n : ℕ} : (p ^ n).PolyRepr where
  tree := .pow p.toRepr.tree n
  tree_eq := by
    rw [TreeRepr.toPolynomial, p.toRepr.tree_eq]

instance {R} [CommRing R] {p q : Polynomial R} [p.PolyRepr] [q.PolyRepr] :
    (p - q).PolyRepr where
  tree := .add p.toRepr.tree (.mul (.const (-1)) q.toRepr.tree)
  tree_eq := by
    nth_rw 3 [← p.toRepr.tree_eq, ← q.toRepr.tree_eq]
    rw [sub_eq_add_neg]
    nth_rw 2 [neg_eq_neg_one_mul]
    nth_rw 1 [TreeRepr.toPolynomial]
    congr
    rw [TreeRepr.toPolynomial, TreeRepr.toPolynomial]
    simp

instance {R} [CommRing R] {p : Polynomial R} [p.PolyRepr] :
    (-p).PolyRepr where
  tree := .mul (.const (-1)) p.toRepr.tree
  tree_eq := by
    unfold TreeRepr.toPolynomial
    rw [p.toRepr.tree_eq]
    unfold TreeRepr.toPolynomial
    simp

instance : (0 : Polynomial R).PolyRepr where
  tree := .const 0
  tree_eq := by simp [TreeRepr.toPolynomial]

instance : (1 : Polynomial R).PolyRepr where
  tree := .const 1
  tree_eq := by simp [TreeRepr.toPolynomial]

example : 1 + 1 == 2 := by
  decide

#reduce (-1 * 1 : (ZMod 11))

#eval (((X + 1 ) ^ 11 : (ZMod 11)[X]).toRepr.tree.toExpandedRBTree')

#eval (((X ^ 11 + 1 ) : (ZMod 11)[X]).toRepr.tree.toExpandedRBTree')

example : ((X  + 1) ^ 11 : ((ZMod 11)[X])[X]) = (( (X ^ 11 + 1): ((ZMod 11)[X])[X])) := by
  -- try simp_rw [← Nat.cast_ofNat (R := Polynomial _) (n := Nat.succ <| Nat.succ _),
  --   ← Polynomial.C_eq_natCast]
  apply PolyRepr.eq_of_toExpandedRBTree'_eq
  -- rw [PolyRepr.eq_iff_directSum'_eq]
  -- native_decide
  -- decide
  sorry
  -- grind [module]

#reduce (((1 - 1 + 1)  : (ZMod 11)[X]).toRepr.tree.toExpandedRBTree').toList =
   (((1 - 1 + 1)  : (ZMod 11)[X]).toRepr.tree.toExpandedRBTree').toList

#reduce (((1 + 1 - 1 + 1) : (ZMod 11)[X]).toRepr.tree.toExpandedRBTree').toList

set_option profiler true

-- unseal TreeRepr.toExpandedRBTree' in
-- set_option trace.Meta.synthInstance true in
-- set_option maxHeartbeats 2000000 in
-- #reduce ((PolyRepr.tree ((X + 1) ^ 8 : (ZMod 11)[X])).toExpandedRBTree' ==
--     (PolyRepr.tree ((1 + X) ^ 8 :  (ZMod 11)[X])).toExpandedRBTree')

#check 1

-- lemma wwww :
--     (((X^2 + X + 1) ^ (22 * 4096) : (ZMod 11)[X]).toRepr.tree.toExpandedRBTree').toList =
--     ((X^2 + X + 1 : (ZMod 11)[X]).toRepr.tree.toExpandedRBTree').toList := by
--   rfl
--   -- decide
set_option profiler true in
example : 1 = 1 := rfl

-- set_option maxRecDepth 10000 in
-- set_option maxHeartbeats 2000000 in
-- -- #reduce (((X ^ 4 + X ^ 3+ X^2 + X + 1) ^ 11) ^ 11 : (ZMod 11)[X]).toRepr.tree.toExpandedRBTree'

-- #check List.mergeSort

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma test : (((X ^ 4 + X ^ 3+ X^2 + X + 1) ) ^ 43 : (ZMod 43)[X]) =
    ((X ^ (3 * 43) + X^(2*43) + 1 + X ^43+ X ^ (4 * 43)) : (ZMod 43)[X]) := by
  -- try simp_rw [← Nat.cast_ofNat (R := Polynomial _) (n := Nat.succ <| Nat.succ _),
  --   ← Polynomial.C_eq_natCast]
  apply PolyRepr.eq_of_toExpandedRBTree'_eq
  -- rw [ PolyRepr.eq_iff_toExpandedRBTree'_eq]
  -- rw [PolyRepr.eq_iff_directSum'_eq]
  -- decide +kernel
  -- decide
  -- -- have := Lean.trustCompiler
  -- -- have := Lean.ofReduceBool
  -- -- have := Lean.ofReduceNat
  -- decide +kernel
  -- grind
  -- csimp
  -- sorry
  sorry

#check Module

-- #eval (C (1 / 2 : ℤ) • X * C 2).toRepr.tree.toExpandedRBTree'

-- #reduce (2⁻¹ : (ZMod 13))

open Polynomial
unseal Rat.mul in
unseal Rat.add in
-- unseal Rat.Eq
lemma test' : C (7 : (ZMod 13)) * X * C 2 = (X : (ZMod 13)[X]) := by
  -- rw [Polynomial.smul_eq_C_mul,]
  -- apply PolyRepr.eq_of_toExpandedRBTree'_eq
  -- grind
  sorry

#print axioms test

-- def (c : ZMod 2) : Decidable

-- #reduce (1 + 1 : (ZMod 2)[X]) = 0
-- lemma test2 : (0 + 1 + 1 : (ZMod 2)) = Batteries.RBMap.ofList ?_ compare := by
  -- decide

-- #reduce ( 0 + 1 - 1 : (ℤ)[X]).toRepr.tree.toExpandedRBTree' ==
--     (1 - 1 : (ℤ)[X]).toRepr.tree.toExpandedRBTree'
lemma test2 :  ( 0 + 1 - 1 : (ℤ)[X]).toRepr.tree.toExpandedRBTree' ==
    (1 - 1 : (ℤ)[X]).toRepr.tree.toExpandedRBTree' := by
  decide

example : True := by
  have :  ( 0 + 1 - 1 : (ℤ)[X]).toRepr.tree.toExpandedRBTree' == Batteries.RBMap.ofList [] compare := by
    rfl
  simp

#reduce ( X + X : (ZMod 2)[X]).toRepr.tree.toExpandedRBTree' ==
    (X + X : (ZMod 2)[X]).toRepr.tree.toExpandedRBTree'

set_option maxRecDepth 40000 in
lemma test3 : ((X + 1 : (ZMod 11)[X]) ^ 11) ^ 22 = (1 + (1 + 1) * X ^ (121) + X ^ 242: (ZMod 11)[X]) := by
  -- try simp_rw [← Nat.cast_ofNat (R := Polynomial _) (n := Nat.succ <| Nat.succ _),
  --   ← Polynomial.C_eq_natCast]
  apply PolyRepr.eq_of_toExpandedRBTree'_eq
  -- rw [PolyRepr.eq_iff_directSum'_eq]
  -- rfl
  decide +kernel
  -- native_decide
  -- aesop
  -- grind




lemma test4 : ((X + 1) * (X + 1) : (ℤ)[X]) = ((1 + X) * (X + 1) : (ℤ)[X]) := by
  -- try simp_rw [← Nat.cast_ofNat (R := Polynomial _) (n := Nat.succ <| Nat.succ _),
  --   ← Polynomial.C_eq_natCast]
  apply PolyRepr.eq_of_toExpandedRBTree'_eq
  -- rw [PolyRepr.eq_iff_directSum'_eq]
  decide

#check 1
-- #check Batteries.RBMap.toList

-- #reduce compare none (some 2 : Option ℕ)

-- noncomputable instance (n : ℕ) : (n.succ.succ : Polynomial R).PolyRepr where
--   tree := .const n.succ.succ
--   tree_eq := by rfl

-- noncomputable instance {n : ℕ} : (n : Polynomial R).PolyRepr where
--   tree := .const n
--   tree_eq := by rfl

set_option maxRecDepth 1000 in
set_option profiler true in
example : (X + 1 : (ZMod 11)[X]) ^ 11 = X ^ 11 + 1 := by
  rw [PolyRepr.eq_iff_directSum'_eq]
  decide

#check Nat.succ

-- def ofReduceBool' (a b : Bool) (h : Lean.reduceBool a = b) : a = b := sorry


lemma example1 : (X + 1 : ℚ[X]) ^ 2 = X ^ 2 + 2 * X + C (1 / 2) + C (1 /2):= by
  rw [← Nat.cast_ofNat (R := Polynomial _) (n := Nat.succ <| Nat.succ _),
    ← Polynomial.C_eq_natCast, PolyRepr.eq_iff_directSum'_eq]
  decide +native

#print axioms example1
-- set_option synthInstance.checkSynthOrder false in
-- instance aaa (priority := low) {R : Type*} [CommRing R] {p q : Polynomial R}
--     [p_inst : p.PolyRepr] (h : q - p = 0) : q.PolyRepr where
--   tree := p_inst.tree
--   tree_eq := sorry --h ▸ p_inst.tree_eq
--   --   -- rw [p_inst.tree_eq]
--   --   -- exact h.symm

unsafe def a : ℕ := 1

set_option maxRecDepth 10000 in
lemma aaa {a : Polynomial (ZMod 11)} (h : a = (X + 1)) : (a : (ZMod 11)[X]) ^ 11 = X ^ 11 + 1 := by
  letI aa := ?aaa
  rw [show a = aa by exact h]
  rw [PolyRepr.eq_iff_directSum'_eq]
  decide

-- unseal TreeRepr.totalDegreeBound' in
lemma aaaa : ((X + 1) ^ 2 : ℤ[X]).toRepr.tree.totalDegreeBound = 2 := by
  decide


#print axioms aaaa
#check Lean.ofReduceBool

#eval Lean.collectAxioms ``example1

#eval Lean.collectAxioms ``aaaa

axiom T : Type
axiom t : T
#eval collectAxioms' ``t  -- only [t]

-- run_meta do
--   let a ← collectAxioms' ``example1


#check IO.rand


def TreeRepr.eval_eq_toPolynomial_eval (p : TreeRepr σ R) (x : R) :
    (p.eval fun _ => x) = p.toPolynomial.eval x := sorry

open Qq Lean in
run_meta do
  let a : Q(ℚ[X]) := q(((X + 1) ^ 2 + (X + 1 + 0) ^ 3 : ℚ[X]))
  let b := q(((X + 1) ^ 2 + (X + 1) ^ 3 : ℚ[X]) = 0)
  -- dbg_trace a
  Lean.logInfo a
  let a1 : Q(ℚ[X]) ← match a with
    | ~q(($aa ^ 2 + $aaa : ℚ[X])) =>
      pure aa
    | _ => pure a
  let a2 : Q(ℚ[X]) ← match a with
    | ~q(($aa + $aaa ^ 3: ℚ[X])) =>
      pure aaa
    | _ => pure a
  Lean.logInfo a1
  Lean.logInfo a2
  let a11 := ptrEq a1 a2
  Lean.logInfo f!"{a11}"


  let b1 : Q(ℚ[X]) ← match b with
    | ~q(($aa ^ 2 + $aaa : ℚ[X]) = 0) =>
      pure aa
    | _ => pure a
  let b2 : Q(ℚ[X]) ← match b with
    | ~q(($aa + $aaa ^ 3: ℚ[X]) = 0) =>
      pure aaa
    | _ => pure a
  Lean.logInfo b1
  Lean.logInfo b2
  let a11 := ptrEq b1 b2
  let a11 := ptrEq b1 a1
  Lean.logInfo f!"{a11}"

end Polynomial
end Polynomial


section MvPolynomial
variable {σ R : Type*} [CommSemiring R] (p q : MvPolynomial σ R)

def TreeRepr.toDirectSum [DecidableEq σ] : TreeRepr σ R → (⨁ _ : (Π₀ _ : σ, ℕ), R)
  | const c => .single 0 c
  | var v => .single (.single v 1) 1
  | add p q => p.toDirectSum + q.toDirectSum
  | mul p q => p.toDirectSum * q.toDirectSum
  | pow p n => p.toDirectSum ^ n
  | ref p => p.toDirectSum

noncomputable def TreeRepr.toMvPolynomial (t : TreeRepr σ R) : MvPolynomial σ R :=
  match t with
  | const c => .C c
  | var v => .X v
  | add p q => p.toMvPolynomial + q.toMvPolynomial
  | mul p q => p.toMvPolynomial * q.toMvPolynomial
  | pow p n => p.toMvPolynomial ^ n
  | ref p => p.toMvPolynomial

namespace MvPolynomial

class PolyRepr (p : MvPolynomial σ R) where
  tree : TreeRepr σ R
  tree_eq : tree.toMvPolynomial = p

def toRepr [p_repr : p.PolyRepr] := p_repr

-- example :=
--   DFinsupp.mapRange (β₂ := fun _ => Π₀ (_ : σ), ℕ)
--     (fun β _ => Finsupp.toDFinsupp (ι := σ) (M := ℕ) β) (by intro i; simp) (p.toDFinsupp)

noncomputable example [DecidableEq σ] :=
  DFinsupp.comapDomain DFinsupp.toFinsupp (sorry) p.toDirectSum

#check DFinsupp.comapDomain

lemma TreeRepr.toDirectSum_eq_toMvPolynomial_toDirectSum [DecidableEq σ]
    (p : TreeRepr σ R) :
      (p.toDirectSum : Π₀ (x : Π₀ (x : σ), ℕ), R) =
      (DFinsupp.comapDomain DFinsupp.toFinsupp (by
          exact
          injective_of_le_imp_le DFinsupp.toFinsupp fun {x y} a => a)
        p.toMvPolynomial.toDirectSum : Π₀ (x : Π₀ (x : σ), ℕ), R)
    := by
  generalize_proofs this
  unfold TreeRepr.toDirectSum TreeRepr.toMvPolynomial
  cases p with
  | const c =>
    simp
    apply Eq.symm
    convert DFinsupp.comapDomain_single (β := fun _ => R)
      DFinsupp.toFinsupp this _ c
    simp
    exact AddMonoidAlgebra.toDirectSum_single _ _
  | var v =>
    simp
    apply Eq.symm
    convert DFinsupp.comapDomain_single (β := fun _ => R) DFinsupp.toFinsupp this _ 1
    simp
    exact AddMonoidAlgebra.toDirectSum_single _ _
  | add p q =>
    simp
    rw [AddMonoidAlgebra.toDirectSum_add, DFinsupp.comapDomain_add]
    congr <;> exact toDirectSum_eq_toMvPolynomial_toDirectSum _
  | mul p q =>
    simp
    -- rw [toDirectSum_eq_toMvPolynomial_toDirectSum q]
    -- generalize_proofs
    -- rw [← DirectSum.mulHom_apply, mulHom]
    rw [AddMonoidAlgebra.toDirectSum_mul]
    -- nth_rw 2 [← smul_eq_mul]
    haveI this2 : DistribMulAction (⨁ (x : σ →₀ ℕ), R) R := sorry
    have := DFinsupp.comapDomain_smul DFinsupp.toFinsupp this
        (AddMonoidAlgebra.toDirectSum p.toMvPolynomial)
        (AddMonoidAlgebra.toDirectSum q.toMvPolynomial)
    rw [toDirectSum_eq_toMvPolynomial_toDirectSum, toDirectSum_eq_toMvPolynomial_toDirectSum]
    convert this.symm
    ·
      ext
      simp
      sorry
    ·
      sorry
    -- induction p
    -- ·
    --   nth_rw 1 [TreeRepr.toDirectSum, TreeRepr.toMvPolynomial]
    --   -- rw [← DirectSum.mulHom_apply]
    --   rw [AddMonoidAlgebra.toDirectSum_mul]
    --   -- unfold C monomial
    --   simp
    --   expose_names
    --   classical
    --   rw [MvPolynomial.C_apply, MvPolynomial.monomial]
    --   have :
    --     @DFunLike.coe (R →ₗ[R] MvPolynomial σ R) R (fun x => MvPolynomial σ R) LinearMap.instFunLike
    --     (AddMonoidAlgebra.lsingle 0) a = ?_ := by
    --     exact AddMonoidAlgebra.lsingle_apply (R := R) (G := σ →₀ ℕ) (k := R) 0 a
    --   rw [this]
    --   ext
    --   simp
    --   rw [DirectSum.mul]
    --   -- simp! [this]
    --   -- unfold lsingle
    --   -- rw [, AddMonoidAlgebra.toDirectSum_single]
    --   -- simp
    --   simp
  | pow p n =>
    simp
    rw [AddMonoidAlgebra.toDirectSum_pow, toDirectSum_eq_toMvPolynomial_toDirectSum]
    -- rw []
    ext i
    simp

    -- #check DFinsupp.comapDomain_smul
    sorry
  | ref p =>
    simp [toDirectSum_eq_toMvPolynomial_toDirectSum]

#check DirectSum.range_map

-- we can make use of it for `DecidableEq (MvPolynomial σ R)` before we find a more efficient way
lemma TreeRepr.mvPolynomial_eq_iff_directSum_eq [DecidableEq σ] (p q : TreeRepr σ R) :
    p.toMvPolynomial = q.toMvPolynomial ↔ p.toDirectSum = q.toDirectSum := by
  -- constructor
  -- ·
  --   cases p
  --   <;> cases q
  --   <;> unfold TreeRepr.toMvPolynomial TreeRepr.toDirectSum
  --   <;> simp_intro ..


  sorry


lemma PolyRepr.eq_iff_directSum_eq [DecidableEq σ] [p.PolyRepr] [q.PolyRepr] :
    p = q ↔ p.toRepr.tree.toDirectSum = q.toRepr.tree.toDirectSum := by
  nth_rw 1 [← p.toRepr.tree_eq, ← q.toRepr.tree_eq]
  exact TreeRepr.mvPolynomial_eq_iff_directSum_eq _ _

instance {c} : (C c : MvPolynomial σ R).PolyRepr where
  tree := .const c
  tree_eq := rfl

instance {v} : (X v : MvPolynomial σ R).PolyRepr where
  tree := .var v
  tree_eq := rfl

instance [p.PolyRepr] [q.PolyRepr] : (p * q).PolyRepr where
  tree := .mul p.toRepr.tree q.toRepr.tree
  tree_eq := by
    nth_rw 3 [← p.toRepr.tree_eq, ← q.toRepr.tree_eq]
    rfl

instance [p.PolyRepr] [q.PolyRepr] : (p + q).PolyRepr where
  tree := .add p.toRepr.tree q.toRepr.tree
  tree_eq := by
    nth_rw 3 [← p.toRepr.tree_eq, ← q.toRepr.tree_eq]
    rfl

instance [p.PolyRepr] {n : ℕ} : (p ^ n).PolyRepr where
  tree := .pow p.toRepr.tree n
  tree_eq := by
    nth_rw 3 [← p.toRepr.tree_eq]
    rfl

instance {R} [CommRing R] {p q : MvPolynomial σ R} [p.PolyRepr] [q.PolyRepr] :
    (p - q).PolyRepr where
  tree := .add p.toRepr.tree (.mul (.const (-1)) q.toRepr.tree)
  tree_eq := by
    nth_rw 3 [← p.toRepr.tree_eq, ← q.toRepr.tree_eq]
    rw [sub_eq_add_neg]
    nth_rw 2 [neg_eq_neg_one_mul]
    nth_rw 1 [TreeRepr.toMvPolynomial]
    congr
    rw [TreeRepr.toMvPolynomial, TreeRepr.toMvPolynomial]
    simp

instance : (0 : MvPolynomial σ R).PolyRepr where
  tree := .const 0
  tree_eq := by
    rw [← MvPolynomial.C_0]
    rfl

instance : (1 : MvPolynomial σ R).PolyRepr where
  tree := .const 1
  tree_eq := rfl

unseal Rat.mul in
unseal Rat.add in
unseal Rat.sub in
lemma aa : (X 0 + X 1 : MvPolynomial ℕ ℚ) * (X 0 + X 1 : MvPolynomial ℕ ℚ) - 4 - 1 = X 0 ^ 2 + C 2 * X 1 * X 0 + X 1 ^ 2 - 5 := by
  -- haveI : Nat.AtLeastTwo 5 := ⟨by decide⟩
  simp_rw [← Nat.cast_ofNat (R := MvPolynomial _ _), ← MvPolynomial.C_eq_coe_nat]
  apply (PolyRepr.eq_iff_directSum_eq _ _).mpr
  -- decide +kernel
  -- simp +decide
  -- have n : ℕ := sorry
  -- have σ : Type* := sorry
  -- set_option trace.Meta.synthInstance true in
  -- #check (OfNat.ofNat n : MvPolynomial σ (Fin 1))
  -- #check (inferInstance : DecidableEq <| Π₀ (x : ℕ), ℕ)
  -- decide
  native_decide
  -- decide
  -- sorry
  -- rgl

#check Lean.ofReduceBool

#reduce [1] ++ [2]

#reduce (proofs := true) ((fun₀ | fun₀ | 0 => 1 => 1) + fun₀ | fun₀ | 1 => 1 => 1 : Π₀ (_ : (Π₀ (_ : ℕ), ℕ)), ℚ) =
    ((fun₀ | fun₀ | 1 => 1 => 1) + fun₀ | fun₀ | 0 => 1 => 1 : Π₀ (_ : (Π₀ (_ : ℕ), ℕ)), ℚ)

-- lemma a :
--   ((fun₀ | fun₀ | 0 => 1 => 1) + fun₀ | fun₀ | 1 => 1 => 1 : Π₀ (_ : (Π₀ (_ : ℕ), ℕ)), ℚ ) =
--     ((fun₀ | fun₀ | 1 => 1 => 1) + fun₀ | fun₀ | 0 => 1 => 1 : Π₀ (_ : (Π₀ (_ : ℕ), ℕ)), ℚ ) := by
--   -- simp +decide [List.filter]
--   -- reduce
--   -- decide
--   -- simp +
--   -- sorry

#reduce 1 + 1 == 2
#reduce ((1 / 3 : ℚ).add (1 / 3)).num
#reduce (1 / 3 : ℚ) + (1 / 3 : ℚ) == (2 / 3 : ℚ)

unseal Rat.add in
-- unseal Nat.gcd in
-- unseal Decidable.rec in
-- unseal HDiv.hDiv in
-- unseal Rat.divExact in
example : (1 : ℚ) + (1 : ℚ) = (2 : ℚ) := by
  -- decide
  decide

#check Decidable.rec

-- def rat_div_alt (a : ℚ) (b : Q) :

-- unseal Rat.mul in
-- unseal Rat.add in
example (fff : MvPolynomial ℕ ℚ) (h : fff = X 0) :
    (fff + X 3 + X 1 ^ 1: MvPolynomial ℕ ℚ) = (X 3 + X 1 + X 0)  := by
  let fff' : MvPolynomial ℕ ℚ := X 0
  rw [show fff = fff' by exact h] at *
  let a : fff'.PolyRepr := by
    simp only [fff', h]
    exact inferInstance
  rw [PolyRepr.eq_iff_directSum_eq]
  fail_if_success decide -- decide fails
  native_decide -- native_decide works



-- unseal List.insert in
-- unseal Nat.primeFactorsList in
-- example : Nat.primeFactors 18 = {2, 3} := by decide -- fail

-- #eval  ((fun₀ | fun₀ | 0 => 1 => 1) + fun₀ | fun₀ | 1 => 1 => 1 : DFinsupp (fun (Π₀ (_ : ℕ), ℕ) ↦ ℕ)) ==
--     ((fun₀ | fun₀ | 1 => 1 => 1) + fun₀ | fun₀ | 0 => 1 => 1 : DFinsupp (fun (Π₀ (_ : ℕ), ℕ) ↦ ℕ))

-- lemma bb : (4: ℚ) ^ 2 = 16 := by
--   decide
  -- ring
unseal Rat.add in
unseal Rat.mul in
example : (4 : ℚ) * (4 : ℚ) = 12 + 4 := by
  decide

-- #check Lean.ofReduceBool
-- #print bb

end MvPolynomial
