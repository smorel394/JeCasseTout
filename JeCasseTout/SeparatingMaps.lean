import Mathlib.Tactic
import JeCasseTout.Grassmannian 
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual
import Mathlib.Algebra.Module.Projective


open Classical
noncomputable section 

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace 𝕜]


-- This is not necessary after all.
/-
lemma ContinuousLinearMap.surjective_section [FiniteDimensional 𝕜 F] (f : E →L[𝕜] F) : 
Submodule.ClosedComplemented (LinearMap.ker f) := by
  rw [←(ContinuousLinearMap.ker_codRestrict f (LinearMap.range f) 
    (by intro x; simp only [LinearMap.mem_range, exists_apply_eq_apply]))]
  set f' := ContinuousLinearMap.codRestrict f (LinearMap.range f) 
             (by intro x; simp only [LinearMap.mem_range, exists_apply_eq_apply])
  have hsec := Module.projective_lifting_property f'.toLinearMap LinearMap.id 
                      (by rw [←(LinearMap.range_eq_top (f := f'.toLinearMap))]
                          erw [LinearMap.range_codRestrict]
                          simp only [Submodule.comap_subtype_eq_top]
                          rfl) 
  set g := Classical.choose hsec 
  apply ContinuousLinearMap.closedComplemented_ker_of_rightInverse f' (LinearMap.toContinuousLinearMap g)
  intro u
  have hg := Classical.choose_spec hsec
  rw [LinearMap.ext_iff] at hg
  have hg := hg u 
  rw [LinearMap.id_apply, LinearMap.coe_comp, Function.comp_apply] at hg  
  rw [LinearMap.coe_toContinuousLinearMap']
  exact hg 
-/

variable (𝕜 E)


def SeparatingMaps (r : ℕ) : Prop := ∀ (W : Grassmannian 𝕜 E r), ∃ (f : E →L[𝕜] (Fin r → 𝕜)), 
(W.1 ⊓ (LinearMap.ker f) = ⊥)

lemma SeparatingMaps_zero : SeparatingMaps 𝕜 E 0 := by
  intro ⟨W, hWfd, hWrank⟩
  existsi 0 
  letI := hWfd 
  rw [finrank_eq_zero] at hWrank
  simp only [ge_iff_le]
  rw [hWrank]
  simp only [ge_iff_le, bot_le, inf_of_le_left]

variable {𝕜 E}


variable (F G)

lemma SeparatingMaps_iff_surjective (r : ℕ) (W : Grassmannian 𝕜 E r) [FiniteDimensional 𝕜 F] 
(hrankF : FiniteDimensional.finrank 𝕜 F = r) (f : E →L[𝕜] F) : 
(W.1 ⊓ (LinearMap.ker f) = ⊥) ↔ Function.Surjective (f.toLinearMap.comp (Submodule.subtype W)) := by
  letI := W.2.1 
  rw [←LinearMap.injective_iff_surjective_of_finrank_eq_finrank] 
  . rw [←LinearMap.ker_eq_bot]
    constructor 
    . intro h
      rw [Submodule.eq_bot_iff]
      intro u 
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Submodule.coeSubtype,
        Function.comp_apply]
      intro hu 
      have hint : u.1 ∈ W.1 ⊓ LinearMap.ker f := by
          simp only [ge_iff_le, Submodule.mem_inf, SetLike.coe_mem, LinearMap.mem_ker, hu, and_self]
      rw [h] at hint 
      simp only [Submodule.mem_bot, ZeroMemClass.coe_eq_zero] at hint  
      exact hint 
    . intro h 
      rw [Submodule.eq_bot_iff]
      intro u
      simp only [ge_iff_le, Submodule.mem_inf, LinearMap.mem_ker, and_imp] 
      intro huW huf
      have hu : ⟨u, huW⟩ ∈ LinearMap.ker (f.toLinearMap.comp (Submodule.subtype W.1)) := by
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Submodule.coeSubtype,
          Function.comp_apply, huf] 
      rw [h] at hu 
      simp only [Submodule.mem_bot, Submodule.mk_eq_zero] at hu  
      exact hu
  . rw [W.2.2, hrankF]
    

lemma SeparatingMaps_iff_target_aux (r : ℕ) (W : Grassmannian 𝕜 E r) [FiniteDimensional 𝕜 F] 
(hrankF : FiniteDimensional.finrank 𝕜 F = r) [FiniteDimensional 𝕜 G] 
(hrankG : FiniteDimensional.finrank 𝕜 G = r) : 
(∃ (f : E →L[𝕜] F), (W.1 ⊓ (LinearMap.ker f) = ⊥)) →
(∃ (f : E →L[𝕜] G), (W.1 ⊓ (LinearMap.ker f) = ⊥)) := by 
  have cond : FiniteDimensional.finrank 𝕜 F = FiniteDimensional.finrank 𝕜 G := by
    rw [hrankF, hrankG]
  intro ⟨f, hf⟩
  set e := ContinuousLinearEquiv.ofFinrankEq cond 
  existsi ContinuousLinearMap.comp (ContinuousLinearEquiv.ofFinrankEq cond) f
  erw [LinearEquiv.ker_comp] 
  exact hf 
    

lemma SeparatingMaps_iff_target (r : ℕ) (W : Grassmannian 𝕜 E r) [FiniteDimensional 𝕜 F] 
(hrankF : FiniteDimensional.finrank 𝕜 F = r) [FiniteDimensional 𝕜 G] 
(hrankG : FiniteDimensional.finrank 𝕜 G = r) : 
(∃ (f : E →L[𝕜] F), (W.1 ⊓ (LinearMap.ker f) = ⊥)) ↔
(∃ (f : E →L[𝕜] G), (W.1 ⊓ (LinearMap.ker f) = ⊥)) := 
⟨SeparatingMaps_iff_target_aux F G r W hrankF hrankG, SeparatingMaps_iff_target_aux G F r W hrankG hrankF⟩

variable {F G}


lemma SeparatingMaps_recursion (r : ℕ) (hsep : SeparatingDual 𝕜 E) :
SeparatingMaps 𝕜 E r → SeparatingMaps 𝕜 E (Nat.succ r) := by
  intro hind W 
  letI := W.2.1 
  set b := FiniteDimensional.finBasisOfFinrankEq 𝕜 W.1 W.2.2
  set W' := Submodule.span 𝕜 (Set.range (((fun i => (b i).1) ∘ (Fin.castLE (Nat.le_succ r))))) 
  have hW'W : W' ≤ W.1 := by
    rw [Submodule.span_le]
    intro v 
    simp only [Set.mem_range, Function.comp_apply, SetLike.mem_coe, forall_exists_index]
    intro i hiv 
    rw [←hiv]
    simp only [SetLike.coe_mem]
  have hW'fd : FiniteDimensional 𝕜 W' := by
    exact Submodule.finiteDimensional_of_le hW'W 
  have hW'rank : FiniteDimensional.finrank 𝕜 W' = r := by
    have hlin : LinearIndependent 𝕜 ((fun i => (b i).1) ∘ (Fin.castLE (Nat.le_succ r))) := by
      apply LinearIndependent.comp 
      . have heq : (fun i => (b i).1) = (Submodule.subtype W.1) ∘ b := by
          ext i 
          simp only [Submodule.coeSubtype, Function.comp_apply]
        rw [heq]
        apply LinearIndependent.map' 
        . apply Basis.linearIndependent 
        . simp only [Submodule.ker_subtype]
      . intro i j heq 
        apply_fun (fun i => i.1) at heq 
        simp only [Fin.coe_castLE] at heq   
        exact Fin.ext heq 
    rw [finrank_span_eq_card hlin]
    simp only [Fintype.card_fin]
  obtain ⟨f, hf⟩ := hind ⟨W', hW'fd, hW'rank⟩ 
  have hnt : LinearMap.ker (f.toLinearMap.comp (Submodule.subtype W)) ≠ ⊥ := by
    by_contra habs 
    rw [LinearMap.ker_eq_bot] at habs 
    have h := LinearMap.finrank_le_finrank_of_injective habs 
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin] at h 
    rw [W.2.2] at h 
    exact Nat.not_succ_le_self r h 
  rw [Submodule.ne_bot_iff] at hnt 
  obtain ⟨⟨u, huW⟩, hfu, hunz⟩ := hnt 
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Submodule.coeSubtype,
    Function.comp_apply] at hfu  
  simp only [ne_eq, Submodule.mk_eq_zero] at hunz  
  obtain ⟨g, hgu⟩ := hsep.exists_eq_one hunz
  rw [SeparatingMaps_iff_target (Fin (Nat.succ r) → 𝕜) ((Fin r → 𝕜) × 𝕜) (Nat.succ r) W]
  . existsi ContinuousLinearMap.prod f g 
    rw [SeparatingMaps_iff_surjective]
    intro ⟨a, b⟩
    rw [SeparatingMaps_iff_surjective] at hf
    change Function.Surjective (f.toLinearMap.comp (Submodule.subtype W')) at hf 
    obtain ⟨⟨v, hvW'⟩, hfv⟩ := hf a
    simp only [LinearMap.coe_comp, ContinuousLinearMap.coe_coe, Submodule.coeSubtype, Function.comp_apply] at hfv  
    have hvW : v ∈ W.1 := Set.mem_of_mem_of_subset hvW' hW'W  
    existsi ⟨v, hvW⟩ + (b - g v) • ⟨u, huW⟩  
    rw [LinearMap.comp_apply, Submodule.subtype_apply]
    simp only [SetLike.mk_smul_mk, AddSubmonoid.mk_add_mk]
    erw [ContinuousLinearMap.prod_apply]
    apply Prod.ext 
    . simp only [map_add, hfv, map_smul, hfu, smul_zero, add_zero]
    . simp only [map_add, map_smul, hgu, smul_eq_mul, mul_one, add_sub_cancel'_right]
    . simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
    . simp only [FiniteDimensional.finrank_prod, FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin,
      FiniteDimensional.finrank_self]
  . simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
  . simp only [FiniteDimensional.finrank_prod, FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin,
    FiniteDimensional.finrank_self]
  

lemma SeparatingMaps.ofSeparatingDual (hsep : SeparatingDual 𝕜 E) : 
∀ (r : ℕ), SeparatingMaps 𝕜 E r := by
  intro r; induction' r with r hrec 
  . exact SeparatingMaps_zero 𝕜 E 
  . exact SeparatingMaps_recursion r hsep hrec 


end 

