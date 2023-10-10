import Mathlib.Tactic
import JeCasseTout.TopCharts
import JeCasseTout.SeparatingMaps 

variable {𝕜 E U F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]   
[NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] 
[NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace 𝕜] {r : ℕ}
[FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G]


lemma LiftElement {φ : E →ₗ[𝕜] F} {ψ : E →ₗ[𝕜] G} (hφ : Function.Surjective φ)
(hφψ : LinearMap.ker φ ⊔ LinearMap.ker ψ = ⊤) (u : F) :
∃ (v : E), φ v = u ∧ ψ v = 0 := by
  obtain ⟨v₀, h₀⟩ := hφ u
  have htop : v₀ ∈ (⊤ : Submodule 𝕜 E) := by simp only [Submodule.mem_top]
  rw [←hφψ, Submodule.mem_sup'] at htop 
  obtain ⟨v, w, hvw⟩ := htop 
  existsi w.1 
  simp only [LinearMap.map_coe_ker, and_true]
  rw [←hvw] at h₀ 
  simp only [map_add, LinearMap.map_coe_ker, zero_add] at h₀  
  exact h₀ 


lemma FiniteCodimension_supplement_aux1  {φ : E →ₗ[𝕜] F} {ψ : E →ₗ[𝕜] G} (hφ : Function.Surjective φ)
(hψ : Function.Surjective ψ) (hrankF : FiniteDimensional.finrank 𝕜 F = r) 
(hrankG : FiniteDimensional.finrank 𝕜 G = r) 
(hφψ : LinearMap.ker φ ⊔ LinearMap.ker ψ = ⊤) :
∃ (W : Grassmannian 𝕜 E r), (W.1 ⊓ (LinearMap.ker φ) = ⊥) ∧ (W.1 ⊓ (LinearMap.ker ψ) = ⊥) := by
  set bF := FiniteDimensional.finBasisOfFinrankEq 𝕜 F hrankF
  set bG := FiniteDimensional.finBasisOfFinrankEq 𝕜 G hrankG
  set v : Fin r → E := fun i => Classical.choose (LiftElement hφ hφψ (bF i))
  set hv := fun i => Classical.choose_spec (LiftElement hφ hφψ (bF i)) 
  rw [sup_comm] at hφψ 
  set w : Fin r → E := fun i => Classical.choose (LiftElement hψ hφψ (bG i))
  set hw := fun i => Classical.choose_spec (LiftElement hψ hφψ (bG i))
  have hlin : LinearIndependent 𝕜 (fun i => v i + w i) := by
    apply LinearIndependent.of_comp φ
    have heq : φ ∘ (fun i => (v i + w i)) = fun i => bF i := by
      ext i 
      simp only [ContinuousLinearMap.coe_coe, Function.comp_apply, map_add]
      rw [(hv i).1, (hw i).2]
      simp only [add_zero]
    rw [heq]
    apply Basis.linearIndependent 
  set W := Submodule.span 𝕜 (Set.range (fun i => v i + w i))
  have hW1 : FiniteDimensional 𝕜 W := by
    apply FiniteDimensional.span_of_finite 
    apply Set.finite_range 
  have hW2 : FiniteDimensional.finrank 𝕜 W = r := by
    rw [finrank_span_eq_card hlin]
    simp only [Fintype.card_fin] 
  existsi ⟨W, hW1, hW2⟩
  constructor 
  . ext u 
    simp only [ge_iff_le, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_bot]   
    constructor 
    . intro ⟨huW, huφ⟩
      rw [←(Basis.constr_range (Pi.basisFun 𝕜 (Fin r)) ℤ )] at huW 
      simp only [LinearMap.mem_range, Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
        smul_add] at huW  
      obtain ⟨a, hua⟩ := huW 
      rw [←hua] at huφ
      rw [map_sum] at huφ
      have heq : ∀ (i : Fin r), φ (a i • v i + a i • w i) = a i • bF i := by
        intro i 
        rw [map_add, map_smul, map_smul, (hv i).1, (hw i).2, smul_zero, add_zero]
      rw [Finset.sum_congr rfl (fun i _ => heq i)] at huφ 
      have hblin := Basis.linearIndependent bF 
      rw [Fintype.linearIndependent_iff] at hblin 
      have hazero := hblin _ huφ
      have heq : ∀ (i : Fin r), a i • v i + a i • w i = 0 := by
        intro i
        rw [hazero i, zero_smul, zero_smul, zero_add] 
      rw [Finset.sum_congr rfl (fun i _ => heq i)] at hua 
      simp only [Finset.sum_const_zero] at hua  
      exact Eq.symm hua 
    . intro hu 
      rw [hu]
      simp only [Submodule.zero_mem, map_zero, and_self]
  . ext u 
    simp only [ge_iff_le, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_bot]   
    constructor 
    . intro ⟨huW, huψ⟩
      rw [←(Basis.constr_range (Pi.basisFun 𝕜 (Fin r)) ℤ )] at huW 
      simp only [LinearMap.mem_range, Basis.constr_apply_fintype, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
        smul_add] at huW  
      obtain ⟨a, hua⟩ := huW 
      rw [←hua] at huψ
      rw [map_sum] at huψ
      have heq : ∀ (i : Fin r), ψ (a i • v i + a i • w i) = a i • bG i := by
        intro i 
        rw [map_add, map_smul, map_smul, (hv i).2, (hw i).1, smul_zero, zero_add]
      rw [Finset.sum_congr rfl (fun i _ => heq i)] at huψ 
      have hblin := Basis.linearIndependent bG 
      rw [Fintype.linearIndependent_iff] at hblin 
      have hazero := hblin _ huψ
      have heq : ∀ (i : Fin r), a i • v i + a i • w i = 0 := by
        intro i
        rw [hazero i, zero_smul, zero_smul, zero_add] 
      rw [Finset.sum_congr rfl (fun i _ => heq i)] at hua 
      simp only [Finset.sum_const_zero] at hua  
      exact Eq.symm hua 
    . intro hu 
      rw [hu]
      simp only [Submodule.zero_mem, map_zero, and_self]

noncomputable def QuotientEquiv {φ : E →ₗ[𝕜] F} (hφ : Function.Surjective φ) {p : Submodule 𝕜 E} 
(hp : LinearMap.ker φ ≤ p) : (E ⧸ p) ≃ₗ[𝕜] (F ⧸ Submodule.map φ p) := by
  set f := Submodule.liftQ p ((Submodule.mkQ (Submodule.map φ p)).comp φ ) 
    (by intro v hv 
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_map]
        existsi v; exact ⟨hv, rfl⟩)
  apply LinearEquiv.ofBijective f 
  constructor 
  . rw [←LinearMap.ker_eq_bot, Submodule.ker_liftQ, LinearMap.ker_comp, Submodule.ker_mkQ,
      Submodule.eq_bot_iff]
    intro u 
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mkQ_apply, forall_exists_index, and_imp]
    intro v w hwp hwv hvu 
    suffices hvp : v ∈ p 
    . rw [←hvu]; simp only [Submodule.Quotient.mk_eq_zero, hvp]
    . have hker : v - w ∈ LinearMap.ker φ := by
        simp only [LinearMap.mem_ker, map_sub, hwv, sub_self]
      rw [←(sub_add_cancel v w)]
      exact Submodule.add_mem p (hp hker) hwp 
  . rw [←LinearMap.range_eq_top] at hφ
    rw [←LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_comp, hφ]
    simp only [Submodule.map_top, Submodule.range_mkQ]


lemma Quotient.finiteDimensional {φ : E →ₗ[𝕜] F} (hφ : Function.Surjective φ) {p : Submodule 𝕜 E} 
(hp : LinearMap.ker φ ≤ p) [FiniteDimensional 𝕜 F] : FiniteDimensional 𝕜 (E ⧸ p) := by
  apply LinearEquiv.finiteDimensional (QuotientEquiv hφ hp).symm 

lemma Quotient.finrank {φ : E →ₗ[𝕜] F} (hφ : Function.Surjective φ) {p : Submodule 𝕜 E} 
(hp : LinearMap.ker φ ≤ p) [FiniteDimensional 𝕜 F] :
FiniteDimensional.finrank 𝕜 (E ⧸ p) + FiniteDimensional.finrank 𝕜 (Submodule.map φ p) =
FiniteDimensional.finrank 𝕜 F := by
  rw [LinearEquiv.finrank_eq (QuotientEquiv hφ hp)]
  apply Submodule.finrank_quotient_add_finrank 

lemma Quotient.compl (φ : E →ₗ[𝕜] F) {p : Submodule 𝕜 E} 
(hp : LinearMap.ker φ ≤ p) {W' : Submodule 𝕜 p} (hW' : W' ⊓ (LinearMap.ker (φ.restrict 
(p := p) (q := Submodule.map φ p) (fun _ h => Submodule.mem_map_of_mem h))) = ⊥)
{W'' : Submodule 𝕜 E} (hW'' : p ⊓ W'' = ⊥) :
((Submodule.map (Submodule.subtype p) W') ⊔ W'') ⊓ (LinearMap.ker φ) = ⊥ := by
  set φ' := (φ.restrict (p := p) (q := Submodule.map φ p) (fun _ h => Submodule.mem_map_of_mem h))
  rw [Submodule.eq_bot_iff]
  intro u hu
  rw [Submodule.mem_inf, Submodule.mem_sup] at hu
  obtain ⟨v, hv, w, hw, hvw⟩ := hu.1 
  rw [Submodule.mem_map] at hv 
  obtain ⟨v', hv', hv'v⟩ := hv 
  have hup : u ∈ p := hp hu.2 
  have hvp : v ∈ p := by 
    rw [←hv'v]
    simp only [Submodule.coeSubtype, SetLike.coe_mem] 
  have hwp : w ∈ p := by 
    rw [add_comm] at hvw 
    rw [eq_sub_of_add_eq hvw]
    exact Submodule.sub_mem p hup hvp 
  have hwzero : w = 0 := by
    rw [←(Submodule.mem_bot 𝕜), ←hW'', Submodule.mem_inf]
    exact ⟨hwp, hw⟩
  rw [hwzero, add_zero] at hvw
  have hv'φ : v' ∈ LinearMap.ker φ' := by
    change φ' v' = 0
    rw [LinearMap.restrict_apply]
    simp only [Submodule.mk_eq_zero] 
    change φ (Submodule.subtype p v') = 0 
    rw [hv'v, hvw]
    exact hu.2
  rw [←hvw, ←hv'v]
  simp only [Submodule.coeSubtype, ZeroMemClass.coe_eq_zero]
  rw [←(Submodule.mem_bot 𝕜), ←hW', Submodule.mem_inf]
  exact ⟨hv', hv'φ⟩



lemma FiniteCodimension_supplement_aux2  {φ : E →ₗ[𝕜] F} {ψ : E →ₗ[𝕜] G} (hφ : Function.Surjective φ)
(hψ : Function.Surjective ψ) (hrankF : FiniteDimensional.finrank 𝕜 F = r) 
(hrankG : FiniteDimensional.finrank 𝕜 G = r) :
FiniteDimensional.finrank 𝕜 (Submodule.map φ (LinearMap.ker φ ⊔ LinearMap.ker ψ)) = 
FiniteDimensional.finrank 𝕜 (Submodule.map ψ (LinearMap.ker φ ⊔ LinearMap.ker ψ)) := by
  have h1 := Submodule.finrank_quotient_add_finrank (Submodule.map φ (LinearMap.ker φ ⊔ LinearMap.ker ψ))
  have h2 := Submodule.finrank_quotient_add_finrank (Submodule.map ψ (LinearMap.ker φ ⊔ LinearMap.ker ψ))
  suffices heq : FiniteDimensional.finrank 𝕜 (F ⧸ (Submodule.map φ (LinearMap.ker φ ⊔ LinearMap.ker ψ))) =
    FiniteDimensional.finrank 𝕜 (G ⧸ (Submodule.map ψ (LinearMap.ker φ ⊔ LinearMap.ker ψ)))
  . rw [hrankG, ←hrankF] at h2 
    rw [←h2, heq, Nat.add_left_cancel_iff] at h1 
    exact h1 
  . rw [←((QuotientEquiv hφ (p := LinearMap.ker φ ⊔ LinearMap.ker ψ) le_sup_left).finrank_eq)] 
    rw [(QuotientEquiv hψ (p := LinearMap.ker φ ⊔ LinearMap.ker ψ) le_sup_right).finrank_eq] 
    

/- The goal:-/

lemma FiniteCodimension_supplement {φ : E →ₗ[𝕜] F} {ψ : E →ₗ[𝕜] G} (hφ : Function.Surjective φ)
(hψ : Function.Surjective ψ) (hrankF : FiniteDimensional.finrank 𝕜 F = r) 
(hrankG : FiniteDimensional.finrank 𝕜 G = r) :
∃ (W : Grassmannian 𝕜 E r), (W.1 ⊓ (LinearMap.ker φ) = ⊥) ∧ (W.1 ⊓ (LinearMap.ker ψ) = ⊥):= by
  set p := LinearMap.ker φ ⊔ LinearMap.ker ψ
  set φ' := φ.restrict (p := p) (q := Submodule.map φ p) (fun _ h => Submodule.mem_map_of_mem h)
  set ψ' := ψ.restrict (p := p) (q := Submodule.map ψ p) (fun _ h => Submodule.mem_map_of_mem h)
  have hφ' : Function.Surjective φ' := by
    intro ⟨v, hv⟩
    rw [Submodule.mem_map] at hv 
    obtain ⟨u, hup, huv⟩ := hv 
    existsi ⟨u, hup⟩
    rw [LinearMap.restrict_apply]
    simp only [Submodule.add_eq_sup, Subtype.mk.injEq] 
    exact huv 
  have hψ' : Function.Surjective ψ' := by
    intro ⟨v, hv⟩
    rw [Submodule.mem_map] at hv 
    obtain ⟨u, hup, huv⟩ := hv 
    existsi ⟨u, hup⟩
    rw [LinearMap.restrict_apply]
    simp only [Submodule.add_eq_sup, Subtype.mk.injEq] 
    exact huv  
  letI : FiniteDimensional 𝕜 (Submodule.map φ p) := by apply FiniteDimensional.finiteDimensional_submodule 
  letI : FiniteDimensional 𝕜 (Submodule.map ψ p) := by apply FiniteDimensional.finiteDimensional_submodule 
  set s := FiniteDimensional.finrank 𝕜 (Submodule.map φ p)  with hsdef
  have hF' : FiniteDimensional.finrank 𝕜 (Submodule.map φ p) = s := rfl 
  have hG' : FiniteDimensional.finrank 𝕜 (Submodule.map ψ p) = s := by
    rw [hsdef, FiniteCodimension_supplement_aux2 hφ hψ hrankF hrankG]
  have hker : LinearMap.ker φ' ⊔ LinearMap.ker ψ' = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro ⟨u, hup⟩
    rw [Submodule.mem_sup'] at hup
    obtain ⟨v, w, h⟩ := hup 
    have hvp : v.1 ∈ p := Submodule.mem_sup_left v.2
    have hwp : w.1 ∈ p := Submodule.mem_sup_right w.2 
    have h' : (⟨u, hup⟩ : p) = ⟨v.1, hvp⟩ + ⟨w.1, hwp⟩ := by
      simp only [AddSubmonoid.mk_add_mk, Subtype.mk.injEq]  
      exact Eq.symm h 
    rw [h', Submodule.mem_sup]
    existsi ⟨v, hvp⟩
    constructor 
    . change φ' _ = 0
      rw [LinearMap.restrict_apply]
      simp only [LinearMap.map_coe_ker, Submodule.mk_eq_zero]
    . existsi ⟨w, hwp⟩
      rw [and_iff_left rfl]
      change ψ' _ = 0 
      rw [LinearMap.restrict_apply]
      simp only [LinearMap.map_coe_ker, Submodule.mk_eq_zero]
  obtain ⟨Wp', hWp'φ, hWp'ψ⟩ := FiniteCodimension_supplement_aux1 hφ' hψ' hF' hG' hker 
  set W' := Grassmannian.map s (Submodule.subtype p) (Submodule.injective_subtype p) Wp' 
  obtain ⟨W'', hcompl⟩ := Submodule.exists_isCompl p 
  have e := Submodule.quotientEquivOfIsCompl _ _ hcompl
  letI := W'.2.1  
  letI : FiniteDimensional 𝕜 W'' := by
    letI := Quotient.finiteDimensional hφ (p := LinearMap.ker φ ⊔ LinearMap.ker ψ) le_sup_left 
    apply LinearEquiv.finiteDimensional e 
  set W := W'.1 ⊔ W''
  have hW1 : FiniteDimensional 𝕜 W := inferInstance 
  have hW2 : FiniteDimensional.finrank 𝕜 W = r := by
    have hinf : W'.1 ⊓ W'' = ⊥ := by 
      rw [Submodule.eq_bot_iff]
      intro u 
      rw [Submodule.mem_inf, Grassmannian.map_apply, Submodule.mem_map] 
      intro ⟨hu1, hu2⟩
      obtain ⟨v, hvW', hvu⟩ := hu1
      have hu3 : u ∈ p := by rw [←hvu]; simp only [Submodule.coeSubtype, ge_iff_le, SetLike.coe_mem]
      have hu4 : u ∈ p ⊓ W'' := by rw [Submodule.mem_inf]; exact ⟨hu3, hu2⟩
      rw [IsCompl.inf_eq_bot hcompl, Submodule.mem_bot] at hu4 
      exact hu4    
    rw [←(add_zero (FiniteDimensional.finrank 𝕜 W)), ←(finrank_bot 𝕜 E), ←hinf,
      Submodule.finrank_sup_add_finrank_inf_eq W'.1 W'', LinearEquiv.finrank_eq e.symm,
      W'.2.2, add_comm, ←hrankF]
    exact Quotient.finrank hφ (p := LinearMap.ker φ ⊔ LinearMap.ker ψ) le_sup_left 
  existsi ⟨W, hW1, hW2⟩
  constructor 
  . exact Quotient.compl φ (p := LinearMap.ker φ ⊔ LinearMap.ker ψ) le_sup_left hWp'φ 
      (IsCompl.inf_eq_bot hcompl)
  . exact Quotient.compl ψ (p := LinearMap.ker φ ⊔ LinearMap.ker ψ) le_sup_right hWp'ψ 
      (IsCompl.inf_eq_bot hcompl)

#exit
class MySpecialEquiv (𝕜 E U : Type*) [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup U] [Module 𝕜 U] (r : ℕ) :=
  (myEquiv : E ≃ₗ[𝕜] (Fin r → 𝕜) × U)

variable {ε : MySpecialEquiv 𝕜 E U r}

end 