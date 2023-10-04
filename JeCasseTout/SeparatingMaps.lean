import Mathlib.Tactic
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


def SeparatingMaps (r : ℕ) : Prop := ∀ (u : E), u ≠ 0 → ∃ (f : E →L[𝕜] (Fin r → 𝕜)), 
Function.Surjective f ∧ f u ≠ 0 


variable {𝕜 E}

variable (F G)

lemma SeparatingMaps_iff_aux (r : ℕ) (u : E) [FiniteDimensional 𝕜 F] 
(hrankF : FiniteDimensional.finrank 𝕜 F = r) [FiniteDimensional 𝕜 G] 
(hrankG : FiniteDimensional.finrank 𝕜 G = r) : 
(∃ (f : E →L[𝕜] F), Function.Surjective f ∧ f u ≠ 0) →
(∃ (f : E →L[𝕜] G), Function.Surjective f ∧ f u ≠ 0) := by
  have cond : FiniteDimensional.finrank 𝕜 F = FiniteDimensional.finrank 𝕜 G := by
    rw [hrankF, hrankG]
  intro ⟨f, hfsur, hfu⟩
  set e := ContinuousLinearEquiv.ofFinrankEq cond 
  existsi ContinuousLinearMap.comp (ContinuousLinearEquiv.ofFinrankEq cond) f
  constructor 
  . exact Function.Surjective.comp (f := f) (ContinuousLinearEquiv.surjective _) hfsur   
  . simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply, ne_eq,
    AddEquivClass.map_eq_zero_iff, hfu, not_false_eq_true]
    

lemma SeparatingMaps_iff (r : ℕ) (u : E) [FiniteDimensional 𝕜 F] 
(hrankF : FiniteDimensional.finrank 𝕜 F = r) [FiniteDimensional 𝕜 G] 
(hrankG : FiniteDimensional.finrank 𝕜 G = r) : 
(∃ (f : E →L[𝕜] F), Function.Surjective f ∧ f u ≠ 0) ↔
(∃ (f : E →L[𝕜] G), Function.Surjective f ∧ f u ≠ 0) := 
⟨SeparatingMaps_iff_aux F G r u hrankF hrankG, SeparatingMaps_iff_aux G F r u hrankG hrankF⟩

variable {F G}

lemma SeparatingMaps_recursion (r : ℕ) (hsep : SeparatingDual 𝕜 E) :
SeparatingMaps 𝕜 E r → (Nat.succ r ≤ FiniteDimensional.finrank 𝕜 E) → SeparatingMaps 𝕜 E (Nat.succ r) := by
  intro hind hdim u hu
  obtain ⟨f, hfsur, hfu⟩ := hind u hu 
  have hnt : ∃ (v : LinearMap.ker f), v ≠ 0 := by
    by_contra habs 
    simp only [ne_eq, Subtype.exists, Submodule.mk_eq_zero, LinearMap.mem_ker, exists_prop, not_exists, not_and,
      not_not] at habs  
    have hfinj : Function.Injective f := by
      erw [←LinearMap.ker_eq_bot]
      ext v 
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Submodule.mem_bot] 
      constructor 
      . exact fun hv => habs v hv 
      . exact fun hv => by rw [hv, map_zero]
    rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective f.toLinearMap ⟨hfinj, hfsur⟩)] at hdim 
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim  
    linarith
  obtain ⟨v, hv⟩ := hnt 
  have hv' : v.1 ≠ 0 := by
    simp only [ne_eq, ZeroMemClass.coe_eq_zero, hv, not_false_eq_true]
  obtain ⟨g, hgv⟩ := hsep.exists_eq_one hv'
  letI : FiniteDimensional 𝕜 ((Fin r → 𝕜) × 𝕜) := Module.Finite.prod 
  rw [SeparatingMaps_iff (Fin (r + 1) → 𝕜) ((Fin r → 𝕜) × 𝕜) (r + 1) u] 
  . existsi ContinuousLinearMap.prod f g 
    constructor 
    . intro ⟨a, b⟩
      obtain ⟨x, hfx⟩ := hfsur a
      set y := (b - g x) • v.1 
      existsi x + y 
      rw [ContinuousLinearMap.prod_apply, Prod.ext_iff]
      constructor 
      . simp only [map_add, hfx, map_smul, LinearMap.map_coe_ker, smul_zero, add_zero]
      . simp only [map_add, map_smul, hgv, smul_eq_mul, mul_one, add_sub_cancel'_right]
    . rw [ContinuousLinearMap.prod_apply, Prod.zero_eq_mk, ne_eq, Prod.ext_iff]
      simp only [hfu, false_and, not_false_eq_true]
  . simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
  . simp only [FiniteDimensional.finrank_prod, FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin,
    FiniteDimensional.finrank_self]

lemma SeparatingMaps.ofSeparatingDual (hsep : SeparatingDual 𝕜 E) : ∀ (r : ℕ), 
Nat.succ r ≤ FiniteDimensional.finrank 𝕜 E → SeparatingMaps 𝕜 E (Nat.succ r) := by
  intro r; induction' r with r hrec 
  . intro _ u hu
    obtain ⟨f, hf⟩ := hsep.exists_ne_zero hu 
    rw [SeparatingMaps_iff (Fin 1 → 𝕜) 𝕜 1 u]
    existsi f 
    constructor 
    . apply LinearMap.surjective_of_ne_zero
      by_contra habs
      apply_fun (fun h => h u) at habs 
      simp only [ContinuousLinearMap.coe_coe, LinearMap.zero_apply] at habs   
      exact hf habs 
    . exact hf 
  . exact fun hdim =>
    SeparatingMaps_recursion (Nat.succ r) hsep (hrec (le_trans (Nat.le_succ (Nat.succ r)) hdim)) hdim 



end 


#exit
class MySpecialEquiv (𝕜 E U : Type*) [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup U] [Module 𝕜 U] (r : ℕ) :=
  (myEquiv : E ≃ₗ[𝕜] (Fin r → 𝕜) × U)

variable {ε : MySpecialEquiv 𝕜 E U r}

end 