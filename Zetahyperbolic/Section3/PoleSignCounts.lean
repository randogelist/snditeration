import Zetahyperbolic.Section3.PoleSigns
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega

/-!
# Exact pole sign counts

Finite parity counts are transported through the actual pole indexing and
coefficient signs. In the weight-five family the positive count is floor(27n/2)
and the negative count is ceil(27n/2); no root simplicity is assumed.
-/

namespace ManuscriptChain.PoleSignCounts

 theorem even_range_count (N h : ℕ) :
    ((Finset.range h).filter (fun i => Even (N + i))).card =
      if Even N then (h + 1) / 2 else h / 2 := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      have hnot : h ∉ (Finset.range h).filter (fun i => Even (N + i)) := by simp
      by_cases hp : Even (N + h)
      · rw [if_pos hp, Finset.card_insert_of_notMem hnot, ih]
        have hsum := Nat.even_iff.mp hp
        by_cases hN : Even N
        · rw [if_pos hN, if_pos hN]
          have hmod := Nat.even_iff.mp hN
          omega
        · rw [if_neg hN, if_neg hN]
          have hmod := Nat.not_even_iff.mp hN
          omega
      · rw [if_neg hp, ih]
        have hsum := Nat.not_even_iff.mp hp
        by_cases hN : Even N
        · rw [if_pos hN, if_pos hN]
          have hmod := Nat.even_iff.mp hN
          omega
        · rw [if_neg hN, if_neg hN]
          have hmod := Nat.not_even_iff.mp hN
          omega

 theorem odd_range_count (N h : ℕ) :
    ((Finset.range h).filter (fun i => Odd (N + i))).card =
      if Even N then h / 2 else (h + 1) / 2 := by
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.range h)
    (fun i => Even (N + i))
  simp only [Nat.not_even_iff_odd, even_range_count, Finset.card_range] at hc
  by_cases hN : Even N
  · rw [if_pos hN] at hc ⊢
    omega
  · rw [if_neg hN] at hc ⊢
    omega

 theorem fin_pred_ncard (h : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Set.ncard {i : Fin h | P i.val} = ((Finset.range h).filter P).card := by
  classical
  have heq : {i : Fin h | P i.val} =
      ((Finset.univ.filter fun i : Fin h => P i.val) : Set (Fin h)) := by
    ext i
    simp
  rw [heq, Set.ncard_coe_finset]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt,
      (Finset.mem_filter.mp hi).2⟩
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro b hb
    have hr := Finset.mem_filter.mp hb
    refine ⟨⟨b, Finset.mem_range.mp hr.1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.2⟩

 theorem even_fin_count (N h : ℕ) :
    Set.ncard {i : Fin h | Even (N + i.val)} =
      if Even N then (h + 1) / 2 else h / 2 := by
  exact (fin_pred_ncard h (fun i => Even (N + i))).trans (even_range_count N h)

 theorem odd_fin_count (N h : ℕ) :
    Set.ncard {i : Fin h | Odd (N + i.val)} =
      if Even N then h / 2 else (h + 1) / 2 := by
  exact (fin_pred_ncard h (fun i => Odd (N + i))).trans (odd_range_count N h)


/-- Zero-based even positions correspond exactly to odd positive pole indices. -/
theorem even_fin_count_eq_odd_poles (p : Real.Parameters) :
    Set.ncard {i : Fin p.h | Even (p.N + i.val)} =
      Set.ncard {a : ℕ | a ∈ Finset.Icc (p.N + 1) p.K ∧ Odd a} := by
  apply Set.ncard_congr (fun i _ => PoleDiagonalization.poleIndex p i)
  · intro i hi
    refine ⟨PoleDiagonalization.poleIndex_mem p i, ?_⟩
    apply Nat.odd_iff.mpr
    have he := Nat.even_iff.mp hi
    dsimp [PoleDiagonalization.poleIndex]
    omega
  · intro i j hi hj hij
    apply Fin.ext
    dsimp [PoleDiagonalization.poleIndex] at hij
    omega
  · intro a ha
    have hb := Finset.mem_Icc.mp ha.1
    let i : Fin p.h := ⟨a - (p.N + 1), by
      dsimp [Real.Parameters.h]
      omega⟩
    have hindex : PoleDiagonalization.poleIndex p i = a := by
      dsimp [PoleDiagonalization.poleIndex, i]
      omega
    refine ⟨i, ?_, hindex⟩
    apply Nat.even_iff.mpr
    have ho := Nat.odd_iff.mp ha.2
    dsimp [i]
    omega

/-- Zero-based odd positions correspond exactly to even positive pole indices. -/
theorem odd_fin_count_eq_even_poles (p : Real.Parameters) :
    Set.ncard {i : Fin p.h | Odd (p.N + i.val)} =
      Set.ncard {a : ℕ | a ∈ Finset.Icc (p.N + 1) p.K ∧ Even a} := by
  apply Set.ncard_congr (fun i _ => PoleDiagonalization.poleIndex p i)
  · intro i hi
    refine ⟨PoleDiagonalization.poleIndex_mem p i, ?_⟩
    apply Nat.even_iff.mpr
    have ho := Nat.odd_iff.mp hi
    dsimp [PoleDiagonalization.poleIndex]
    omega
  · intro i j hi hj hij
    apply Fin.ext
    dsimp [PoleDiagonalization.poleIndex] at hij
    omega
  · intro a ha
    have hb := Finset.mem_Icc.mp ha.1
    let i : Fin p.h := ⟨a - (p.N + 1), by
      dsimp [Real.Parameters.h]
      omega⟩
    have hindex : PoleDiagonalization.poleIndex p i = a := by
      dsimp [PoleDiagonalization.poleIndex, i]
      omega
    refine ⟨i, ?_, hindex⟩
    apply Nat.odd_iff.mpr
    have he := Nat.even_iff.mp ha.2
    dsimp [i]
    omega

theorem positive_pole_count (p : Real.Parameters) (hm : 0 < p.m) :
    Set.ncard {i : Fin p.h | 0 < PoleDiagonalization.poleWeight p i} =
      if Even p.N then (p.h + 1) / 2 else p.h / 2 := by
  simp only [PoleDiagonalization.poleWeight_pos_iff p hm]
  exact even_fin_count p.N p.h

theorem negative_pole_count (p : Real.Parameters) (hm : 0 < p.m) :
    Set.ncard {i : Fin p.h | PoleDiagonalization.poleWeight p i < 0} =
      if Even p.N then p.h / 2 else (p.h + 1) / 2 := by
  simp only [PoleDiagonalization.poleWeight_neg_iff p hm]
  exact odd_fin_count p.N p.h

theorem odd_poles_count (p : Real.Parameters) :
    Set.ncard {a : ℕ | a ∈ Finset.Icc (p.N + 1) p.K ∧ Odd a} =
      if Even p.N then (p.h + 1) / 2 else p.h / 2 := by
  rw [← even_fin_count_eq_odd_poles, even_fin_count]

theorem even_poles_count (p : Real.Parameters) :
    Set.ncard {a : ℕ | a ∈ Finset.Icc (p.N + 1) p.K ∧ Even a} =
      if Even p.N then p.h / 2 else (p.h + 1) / 2 := by
  rw [← odd_fin_count_eq_even_poles, odd_fin_count]

/-- For the weight-five family the positive diagonal count is floor(27n/2). -/
theorem weightFive_even_count (n : ℕ) :
    Set.ncard {i : Fin (PoleDiagonalization.weightFiveParameters n).h |
      Even ((PoleDiagonalization.weightFiveParameters n).N + i.val)} =
      27 * n / 2 := by
  rw [even_fin_count, PoleDiagonalization.weightFiveParameters_dimension]
  change (if Even (3 * n) then (27 * n + 1) / 2 else 27 * n / 2) = _
  split_ifs with he
  · have hn : Even n := (Nat.even_mul.mp he).resolve_left (by decide)
    have hh : Even (27 * n) := hn.mul_left 27
    have hmod := Nat.even_iff.mp hh
    omega
  · rfl

/-- For the weight-five family the negative diagonal count is ceil(27n/2). -/
theorem weightFive_odd_count (n : ℕ) :
    Set.ncard {i : Fin (PoleDiagonalization.weightFiveParameters n).h |
      Odd ((PoleDiagonalization.weightFiveParameters n).N + i.val)} =
      (27 * n + 1) / 2 := by
  rw [odd_fin_count, PoleDiagonalization.weightFiveParameters_dimension]
  change (if Even (3 * n) then 27 * n / 2 else (27 * n + 1) / 2) = _
  split_ifs with he
  · have hn : Even n := (Nat.even_mul.mp he).resolve_left (by decide)
    have hh : Even (27 * n) := hn.mul_left 27
    have hmod := Nat.even_iff.mp hh
    omega
  · rfl

theorem weightFive_positive_pole_count (n : ℕ) :
    Set.ncard {i : Fin (PoleDiagonalization.weightFiveParameters n).h |
      0 < PoleDiagonalization.poleWeight (PoleDiagonalization.weightFiveParameters n) i} =
      27 * n / 2 := by
  simp only [PoleDiagonalization.poleWeight_pos_iff (PoleDiagonalization.weightFiveParameters n)
    (by change 0 < (3 : ℕ); decide)]
  exact weightFive_even_count n

theorem weightFive_negative_pole_count (n : ℕ) :
    Set.ncard {i : Fin (PoleDiagonalization.weightFiveParameters n).h |
      PoleDiagonalization.poleWeight (PoleDiagonalization.weightFiveParameters n) i < 0} =
      (27 * n + 1) / 2 := by
  simp only [PoleDiagonalization.poleWeight_neg_iff (PoleDiagonalization.weightFiveParameters n)
    (by change 0 < (3 : ℕ); decide)]
  exact weightFive_odd_count n

/-- The equivalent remainder-based expression belongs to the negative count. -/
theorem weightFive_odd_count_mod (n : ℕ) :
    Set.ncard {i : Fin (PoleDiagonalization.weightFiveParameters n).h |
      Odd ((PoleDiagonalization.weightFiveParameters n).N + i.val)} =
      (27 * n + n % 2) / 2 := by
  rw [weightFive_odd_count]
  omega

end ManuscriptChain.PoleSignCounts
