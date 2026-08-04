import Rank3KUM.CyclicOrder

namespace Rank3KUM

open Set

variable {α : Type*}

/-- Append a three-element basis at the wraparound gap of a cyclic basis order. -/
theorem cyclicBasisOrder3_appendBlock_wrap
    (M : Matroid α) {E D : Set α} {m : ℕ}
    (hm : 2 ≤ m)
    (hED : Disjoint E D)
    (small : Fin m ≃ E)
    (block : Fin 3 ≃ D)
    (hsmall : CyclicBasisOrder3 M (by omega) small)
    (hD : M.IsBase D)
    (hleft₁ :
      M.IsBase
        ({(small ⟨m - 2, by omega⟩ : α),
          (small ⟨m - 1, by omega⟩ : α),
          (block 0 : α)} : Set α))
    (hleft₂ :
      M.IsBase
        ({(small ⟨m - 1, by omega⟩ : α),
          (block 0 : α),
          (block 1 : α)} : Set α))
    (hright₁ :
      M.IsBase
        ({(block 1 : α),
          (block 2 : α),
          (small ⟨0, by omega⟩ : α)} : Set α))
    (hright₂ :
      M.IsBase
        ({(block 2 : α),
          (small ⟨0, by omega⟩ : α),
          (small ⟨1, by omega⟩ : α)} : Set α)) :
    CyclicBasisOrder3 M (by omega)
      (appendBlockOrder hED small block) := by
  intro i
  refine Fin.addCases (m := m) (n := 3) ?_ ?_ i
  · intro j
    by_cases hj : j.val + 2 < m
    · let j₁ : Fin m := ⟨j.val + 1, by omega⟩
      let j₂ : Fin m := ⟨j.val + 2, by omega⟩
      have hnew₁ :
          cyclicIndex (m + 3) (by omega)
              (Fin.castAdd 3 j) 1 =
            Fin.castAdd 3 j₁ := by
        apply Fin.ext
        simp [cyclicIndex, j₁]
        omega
      have hnew₂ :
          cyclicIndex (m + 3) (by omega)
              (Fin.castAdd 3 j) 2 =
            Fin.castAdd 3 j₂ := by
        apply Fin.ext
        simp [cyclicIndex, j₂]
        omega
      have hold₁ :
          cyclicIndex m (by omega) j 1 = j₁ := by
        apply Fin.ext
        simp [cyclicIndex, j₁]
        omega
      have hold₂ :
          cyclicIndex m (by omega) j 2 = j₂ := by
        apply Fin.ext
        simp [cyclicIndex, j₂]
        omega
      have hs := hsmall j
      rw [hold₁, hold₂] at hs
      simpa [hnew₁, hnew₂] using hs
    · have hjcase : j.val = m - 2 ∨ j.val = m - 1 := by
        omega
      rcases hjcase with hjlast₂ | hjlast
      · have hjEq : j = (⟨m - 2, by omega⟩ : Fin m) := by
          apply Fin.ext
          exact hjlast₂
        subst j
        have hnew₁ :
            cyclicIndex (m + 3) (by omega)
                (Fin.castAdd 3 (⟨m - 2, by omega⟩ : Fin m)) 1 =
              Fin.castAdd 3 (⟨m - 1, by omega⟩ : Fin m) := by
          apply Fin.ext
          simp [cyclicIndex]
          omega
        have hnew₂ :
            cyclicIndex (m + 3) (by omega)
                (Fin.castAdd 3 (⟨m - 2, by omega⟩ : Fin m)) 2 =
              Fin.natAdd m (0 : Fin 3) := by
          apply Fin.ext
          simp [cyclicIndex]
          omega
        simpa [hnew₁, hnew₂] using hleft₁
      · have hjEq : j = (⟨m - 1, by omega⟩ : Fin m) := by
          apply Fin.ext
          exact hjlast
        subst j
        have hnew₁ :
            cyclicIndex (m + 3) (by omega)
                (Fin.castAdd 3 (⟨m - 1, by omega⟩ : Fin m)) 1 =
              Fin.natAdd m (0 : Fin 3) := by
          apply Fin.ext
          simp [cyclicIndex]
          omega
        have hnew₂ :
            cyclicIndex (m + 3) (by omega)
                (Fin.castAdd 3 (⟨m - 1, by omega⟩ : Fin m)) 2 =
              Fin.natAdd m (1 : Fin 3) := by
          apply Fin.ext
          simp [cyclicIndex]
          omega
        simpa [hnew₁, hnew₂] using hleft₂
  · intro j
    fin_cases j
    · have hnew₁ :
          cyclicIndex (m + 3) (by omega)
              (Fin.natAdd m (0 : Fin 3)) 1 =
            Fin.natAdd m (1 : Fin 3) := by
        apply Fin.ext
        simp [cyclicIndex]
        omega
      have hnew₂ :
          cyclicIndex (m + 3) (by omega)
              (Fin.natAdd m (0 : Fin 3)) 2 =
            Fin.natAdd m (2 : Fin 3) := by
        apply Fin.ext
        simp [cyclicIndex]
        omega
      have hset := TwoGap.set_eq_triple_of_fin3_equiv block
      rw [hset] at hD
      simpa [hnew₁, hnew₂] using hD
    · have hnew₁ :
          cyclicIndex (m + 3) (by omega)
              (Fin.natAdd m (1 : Fin 3)) 1 =
            Fin.natAdd m (2 : Fin 3) := by
        apply Fin.ext
        simp [cyclicIndex]
        omega
      have hnew₂ :
          cyclicIndex (m + 3) (by omega)
              (Fin.natAdd m (1 : Fin 3)) 2 =
            Fin.castAdd 3 (⟨0, by omega⟩ : Fin m) := by
        apply Fin.ext
        simp [cyclicIndex]
        omega
      simpa [hnew₁, hnew₂] using hright₁
    · have hnew₁ :
          cyclicIndex (m + 3) (by omega)
              (Fin.natAdd m (2 : Fin 3)) 1 =
            Fin.castAdd 3 (⟨0, by omega⟩ : Fin m) := by
        apply Fin.ext
        simp [cyclicIndex]
        omega
      have hnew₂ :
          cyclicIndex (m + 3) (by omega)
              (Fin.natAdd m (2 : Fin 3)) 2 =
            Fin.castAdd 3 (⟨1, by omega⟩ : Fin m) := by
        apply Fin.ext
        simp [cyclicIndex]
        omega
      simpa [hnew₁, hnew₂] using hright₂

end Rank3KUM
