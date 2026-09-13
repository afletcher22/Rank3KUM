import Rank3KUM.BalancedInterleaveGeneral

namespace Rank3KUM

open Set

noncomputable section

variable {α : Type*}

/-- Evaluate a balanced block position known to lie in its left segment. -/
theorem balancedBlockOrder_apply_left_of_lt
    {P Q : Set α} {s t k : ℕ}
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (i : Fin k) (d : Fin (s + t))
    (hd : d.val < s) :
    ((balancedBlockOrder hPQ left right
        (blockPosition (s + t) k i d) : (P ∪ Q : Set α)) : α) =
      (left (blockPosition s k i ⟨d.val, hd⟩) : α) := by
  let j : Fin s := ⟨d.val, hd⟩
  have hdEq : d = Fin.castAdd t j := by
    apply Fin.ext
    rfl
  subst d
  simpa [j] using balancedBlockOrder_left hPQ left right i j

/-- Evaluate a balanced block position known to lie in its right segment. -/
theorem balancedBlockOrder_apply_right_of_le
    {P Q : Set α} {s t k : ℕ}
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (i : Fin k) (d : Fin (s + t))
    (hd : s ≤ d.val) :
    ((balancedBlockOrder hPQ left right
        (blockPosition (s + t) k i d) : (P ∪ Q : Set α)) : α) =
      (right (blockPosition t k i
        ⟨d.val - s, by omega⟩) : α) := by
  let j : Fin t := ⟨d.val - s, by omega⟩
  have hdEq : d = Fin.natAdd s j := by
    apply Fin.ext
    change d.val = s + (d.val - s)
    omega
  subst d
  simpa [j] using balancedBlockOrder_right hPQ left right i j

/--
If an `(s+t)`-window starts in the left segment of a balanced block, its
right entries form one cyclic `t`-window beginning at the current right
block, while its left entries form the cyclic `s`-window beginning at the
same left offset.
-/
theorem cyclicWindow_balancedBlockOrder_left_start
    {P Q : Set α} {s t k : ℕ}
    (hs : 0 < s) (ht : 0 < t) (hk : 0 < k)
    (hPQ : Disjoint P Q)
    (left : Fin (s * k) ≃ P)
    (right : Fin (t * k) ≃ Q)
    (i : Fin k) (a : Fin s) :
    cyclicWindow (s + t) (Nat.mul_pos (by omega) hk)
        (balancedBlockOrder hPQ left right)
        (blockPosition (s + t) k i (Fin.castAdd t a)) =
      cyclicWindow t (Nat.mul_pos ht hk) right
          (blockPosition t k i ⟨0, ht⟩) ∪
        cyclicWindow s (Nat.mul_pos hs hk) left
          (blockPosition s k i a) := by
  ext x
  simp only [cyclicWindow, Set.mem_range, Set.mem_union]
  constructor
  · rintro ⟨q, rfl⟩
    by_cases hleft : a.val + q.val < s
    · right
      let qs : Fin s := ⟨q.val, by omega⟩
      refine ⟨qs, ?_⟩
      symm
      have hout := cyclicIndex_blockPosition_same
        (s + t) k (by omega) hk i (Fin.castAdd t a) q.val (by omega)
      have hsrc := cyclicIndex_blockPosition_same
        s k hs hk i a qs.val (by simp [qs]; omega)
      rw [hout, hsrc]
      have heval := balancedBlockOrder_apply_left_of_lt
        hPQ left right i
        (⟨a.val + q.val, by omega⟩ : Fin (s + t)) (by omega)
      simpa [qs] using heval
    · by_cases hsame : a.val + q.val < s + t
      · left
        let qt : Fin t := ⟨a.val + q.val - s, by omega⟩
        refine ⟨qt, ?_⟩
        symm
        have hout := cyclicIndex_blockPosition_same
          (s + t) k (by omega) hk i (Fin.castAdd t a) q.val hsame
        have hsrc := cyclicIndex_blockPosition_same
          t k ht hk i (⟨0, ht⟩ : Fin t) qt.val (by simp [qt]; omega)
        rw [hout, hsrc]
        have heval := balancedBlockOrder_apply_right_of_le
          hPQ left right i
          (⟨a.val + q.val, hsame⟩ : Fin (s + t)) (by omega)
        simpa [qt] using heval
      · right
        let qs : Fin s := ⟨q.val - t, by omega⟩
        refine ⟨qs, ?_⟩
        symm
        have hout := cyclicIndex_blockPosition_next
          (s + t) k (by omega) hk i (Fin.castAdd t a) q.val q.isLt (by omega)
        have hsrc := cyclicIndex_blockPosition_next
          s k hs hk i a qs.val qs.isLt (by simp [qs]; omega)
        rw [hout, hsrc]
        have hres :
            a.val + q.val - (s + t) = a.val + (q.val - t) - s := by
          omega
        have heval := balancedBlockOrder_apply_left_of_lt
          hPQ left right (cyclicIndex k hk i 1)
          (⟨a.val + q.val - (s + t), by omega⟩ : Fin (s + t)) (by omega)
        simpa [qs, hres] using heval
  · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · let q : Fin (s + t) := ⟨s - a.val + j.val, by omega⟩
      refine ⟨q, ?_⟩
      have hout := cyclicIndex_blockPosition_same
        (s + t) k (by omega) hk i (Fin.castAdd t a) q.val (by simp [q]; omega)
      have hsrc := cyclicIndex_blockPosition_same
        t k ht hk i (⟨0, ht⟩ : Fin t) j.val (by omega)
      rw [hout, hsrc]
      have hres : a.val + q.val - s = j.val := by
        simp [q]
        omega
      have heval := balancedBlockOrder_apply_right_of_le
        hPQ left right i
        (⟨a.val + q.val, by simp [q]; omega⟩ : Fin (s + t)) (by simp [q]; omega)
      simpa [hres] using heval
    · by_cases hsame : a.val + j.val < s
      · let q : Fin (s + t) := ⟨j.val, by omega⟩
        refine ⟨q, ?_⟩
        have hout := cyclicIndex_blockPosition_same
          (s + t) k (by omega) hk i (Fin.castAdd t a) q.val (by simp [q]; omega)
        have hsrc := cyclicIndex_blockPosition_same
          s k hs hk i a j.val hsame
        rw [hout, hsrc]
        have heval := balancedBlockOrder_apply_left_of_lt
          hPQ left right i
          (⟨a.val + j.val, by omega⟩ : Fin (s + t)) (by omega)
        simpa [q] using heval
      · let q : Fin (s + t) := ⟨t + j.val, by omega⟩
        refine ⟨q, ?_⟩
        have hout := cyclicIndex_blockPosition_next
          (s + t) k (by omega) hk i (Fin.castAdd t a) q.val q.isLt
            (by simp [q]; omega)
        have hsrc := cyclicIndex_blockPosition_next
          s k hs hk i a j.val j.isLt (by omega)
        rw [hout, hsrc]
        have hres :
            a.val + q.val - (s + t) = a.val + j.val - s := by
          simp [q]
          omega
        have heval := balancedBlockOrder_apply_left_of_lt
          hPQ left right (cyclicIndex k hk i 1)
          (⟨a.val + q.val - (s + t), by simp [q]; omega⟩ : Fin (s + t))
          (by simp [q]; omega)
        simpa [hres] using heval

#print axioms Rank3KUM.balancedBlockOrder_apply_left_of_lt
#print axioms Rank3KUM.balancedBlockOrder_apply_right_of_le
#print axioms Rank3KUM.cyclicWindow_balancedBlockOrder_left_start

end

end Rank3KUM
