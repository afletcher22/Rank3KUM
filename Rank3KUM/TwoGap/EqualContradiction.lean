import Rank3KUM.TwoGap.EqualNonempty
import Rank3KUM.TwoGap.ResidualSupportDisjoint

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/-- The equal common-singleton configuration for both blocked gaps is impossible. -/
theorem false_of_equal_singleton_partner_pairs
    (M : Matroid α) {D : Set α} {p a b c q t : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hP : M.IsBase ({p, a, b} : Set α))
    (hC : M.IsBase ({a, b, c} : Set α))
    (hQ : M.IsBase ({b, c, q} : Set α))
    (hpD : p ∉ D) (haD : a ∉ D) (hbD : b ∉ D)
    (hcD : c ∉ D) (hqD : q ∉ D)
    (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hbq : b ≠ q) (hcq : c ≠ q)
    (hXP :
      SymmetricPartners M D ({p, a, b} : Set α) b = {t})
    (hXCa :
      SymmetricPartners M D ({a, b, c} : Set α) a = {t})
    (hXCc :
      SymmetricPartners M D ({a, b, c} : Set α) c = {t})
    (hXQ :
      SymmetricPartners M D ({b, c, q} : Set α) b = {t}) :
    False := by
  have htXP :
      t ∈ SymmetricPartners M D ({p, a, b} : Set α) b := by
    rw [hXP]
    simp
  have htXCa :
      t ∈ SymmetricPartners M D ({a, b, c} : Set α) a := by
    rw [hXCa]
    simp
  have htXCc :
      t ∈ SymmetricPartners M D ({a, b, c} : Set α) c := by
    rw [hXCc]
    simp

  have htXP' :=
    (mem_symmetricPartners M D ({p, a, b} : Set α) b t).mp htXP
  have htXCa' :=
    (mem_symmetricPartners M D ({a, b, c} : Set α) a t).mp htXCa
  have htXCc' :=
    (mem_symmetricPartners M D ({a, b, c} : Set α) c t).mp htXCc
  have htD : t ∈ D := htXP'.1
  have hDta : M.IsBase (exchangeSet D t a) := htXCa'.2.2.1
  have hDtb : M.IsBase (exchangeSet D t b) := htXP'.2.2.1
  have hDtc : M.IsBase (exchangeSet D t c) := htXCc'.2.2.1

  obtain ⟨hUa, hUb, hUc⟩ :=
    equal_singleton_residualSupports_nonempty
      M hD hP hC haD hbD hcD hab hac hbc hXP hXCa hXCc

  -- Lemma 7.20 is used directly for all three residual-support pairs.
  have hACXset : ({a, c, b} : Set α) = ({a, b, c} : Set α) := by
    ext z
    simp [or_comm, or_left_comm, or_assoc]
  have hACYset : ({b, a, c} : Set α) = ({a, b, c} : Set α) := by
    ext z
    simp [or_comm, or_left_comm, or_assoc]
  have hACBridgeSet : ({c, b, a} : Set α) = ({a, b, c} : Set α) := by
    ext z
    simp [or_comm, or_left_comm, or_assoc]
  have hACX : M.IsBase ({a, c, b} : Set α) := by
    rw [hACXset]
    exact hC
  have hACY : M.IsBase ({b, a, c} : Set α) := by
    rw [hACYset]
    exact hC
  have hACBridge : M.IsBase ({c, b, a} : Set α) := by
    rw [hACBridgeSet]
    exact hC
  have hACXsym :
      SymmetricPartners M D ({a, c, b} : Set α) a = {t} := by
    rw [hACXset]
    exact hXCa
  have hACYsym :
      SymmetricPartners M D ({b, a, c} : Set α) c = {t} := by
    rw [hACYset]
    exact hXCc
  have hAC :
      Disjoint (ResidualSupport M D t a) (ResidualSupport M D t c) :=
    residualSupport_disjoint_of_shared_bridge
      M hRank hD hACX hACY hACBridge
      haD hcD hbD haD hcD
      hac hab hbc.symm hab.symm hbc.symm hac.symm
      htD hDtb hACXsym hACYsym

  have hABYset : ({c, q, b} : Set α) = ({b, c, q} : Set α) := by
    ext z
    simp [or_comm, or_left_comm, or_assoc]
  have hABY : M.IsBase ({c, q, b} : Set α) := by
    rw [hABYset]
    exact hQ
  have hABYsym :
      SymmetricPartners M D ({c, q, b} : Set α) b = {t} := by
    rw [hABYset]
    exact hXQ
  have hAB :
      Disjoint (ResidualSupport M D t a) (ResidualSupport M D t b) :=
    residualSupport_disjoint_of_shared_bridge
      M hRank hD hC hABY hQ
      haD hbD hcD hqD hbD
      hab hac hbc hcq hbc hbq
      htD hDtc hXCa hABYsym

  have hBCXset : ({b, p, a} : Set α) = ({p, a, b} : Set α) := by
    ext z
    simp [or_comm, or_left_comm, or_assoc]
  have hBCX : M.IsBase ({b, p, a} : Set α) := by
    rw [hBCXset]
    exact hP
  have hBCXsym :
      SymmetricPartners M D ({b, p, a} : Set α) b = {t} := by
    rw [hBCXset]
    exact hXP
  have hBC :
      Disjoint (ResidualSupport M D t b) (ResidualSupport M D t c) :=
    residualSupport_disjoint_of_shared_bridge
      M hRank hD hBCX hC hP
      hbD hpD haD hbD hcD
      hpb.symm hab.symm hpa hab hac.symm hbc.symm
      htD hDta hBCXsym hXCc

  rcases hUa with ⟨ua, hua⟩
  rcases hUb with ⟨ub, hub⟩
  rcases hUc with ⟨uc, huc⟩

  have haE : a ∈ M.E := hC.subset_ground (by simp)
  have hbE : b ∈ M.E := hP.subset_ground (by simp)
  have hcE : c ∈ M.E := hC.subset_ground (by simp)
  have huaD : ua ∈ D \ {t} :=
    residualSupport_subset_basis_sdiff M hD haE haD hua
  have hubD : ub ∈ D \ {t} :=
    residualSupport_subset_basis_sdiff M hD hbE hbD hub
  have hucD : uc ∈ D \ {t} :=
    residualSupport_subset_basis_sdiff M hD hcE hcD huc

  have huab : ua ≠ ub := by
    intro h
    subst ub
    exact (Set.disjoint_left.1 hAB) hua hub
  have huac : ua ≠ uc := by
    intro h
    subst uc
    exact (Set.disjoint_left.1 hAC) hua huc
  have hubc : ub ≠ uc := by
    intro h
    subst uc
    exact (Set.disjoint_left.1 hBC) hub huc

  have htripleSub :
      ({ua, ub, uc} : Set α) ⊆ D \ {t} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact huaD
    · exact hubD
    · exact hucD
  have htripleCard : ({ua, ub, uc} : Set α).encard = 3 :=
    encard_triple_eq_three huab huac hubc

  have hsingleton : ({t} : Set α) ⊆ D := by
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx ▸ htD
  have hcardD : D.encard = 3 := hD.encard_eq_eRank.trans hRank
  have hcardDt : (D \ {t}).encard = 2 := by
    calc
      (D \ {t}).encard = D.encard - ({t} : Set α).encard :=
        Set.encard_sdiff hsingleton (by simp)
      _ = 3 - 1 := by rw [hcardD, Set.encard_singleton]
      _ = 2 := by decide
  have hle := Set.encard_le_encard htripleSub
  rw [htripleCard, hcardDt] at hle
  norm_num at hle

end Rank3KUM.TwoGap
