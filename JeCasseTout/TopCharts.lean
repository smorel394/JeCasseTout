import Mathlib.Tactic
import JeCasseTout.Charts
import Mathlib.Analysis.Calculus.ContDiff 
import Mathlib.Analysis.NormedSpace.OperatorNorm




noncomputable section 

section Topology

namespace Grassmannian

/- Note: if my changes to mathlib are accepted, change the NontriviallyNormedField 𝕜 to 
NontriviallyNormedDivisionRing 𝕜 We will also need to introduce a NontriviallyNormedField over which
𝕜 is an algebra and E and U are NormedSpaces.-/
/-variable {𝕜 E U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]
[NormedAddCommGroup U] [Module 𝕜 U] [BoundedSMul 𝕜 U] [CompleteSpace 𝕜] {r : ℕ}-/

variable {𝕜 E U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace 𝕜] {r : ℕ}

/- The goodset of a continuous linear map φ : E → (Fin r → 𝕜) is open.-/

lemma GoodsetIsOpen_aux1 (φ : E →L[𝕜] (Fin r → 𝕜)) : IsOpen {v : Fin r → E | LinearIndependent 𝕜 (φ ∘ v)} := by
  have heq : {v : Fin r → E | LinearIndependent 𝕜 (φ ∘ v)} = (fun (v : Fin r → E) => φ ∘ v)⁻¹'
    {u : Fin r → (Fin r → 𝕜) | LinearIndependent 𝕜 u} := by
    simp only [Set.preimage_setOf_eq]
  rw [heq]
  apply IsOpen.preimage
  . apply Pi.continuous_postcomp φ.continuous
  . exact isOpen_setOf_linearIndependent 

lemma GoodsetIsOpen_aux2 (φ : E →L[𝕜] (Fin r → 𝕜)) : IsOpen {v : {v : Fin r → E // LinearIndependent 𝕜 v} 
| LinearIndependent 𝕜 (φ ∘ v.1)} := by 
  have heq : {v : {v : Fin r → E // LinearIndependent 𝕜 v} | LinearIndependent 𝕜 (φ ∘ v.1)} = 
    ({v : Fin r → E | LinearIndependent 𝕜 v}.restrict (fun (v : Fin r → E) => φ ∘ v))⁻¹'
    {u : Fin r → (Fin r → 𝕜) | LinearIndependent 𝕜 u} := by 
    simp only [Set.coe_setOf, Set.preimage_setOf_eq, Set.restrict_apply, Set.mem_setOf_eq]
  rw [heq]
  apply IsOpen.preimage
  . rw [Set.restrict_eq]
    apply Continuous.comp
    . apply Pi.continuous_postcomp φ.continuous 
    . exact continuous_subtype_val
  . exact isOpen_setOf_linearIndependent  


lemma GoodsetIsOpen (φ : E →L[𝕜] (Fin r → 𝕜)) : IsOpen (Goodset (φ : E →ₗ[𝕜] Fin r → 𝕜)) := by 
  rw [isOpen_coinduced]
  have heq : (Grassmannian.mk' 𝕜)⁻¹' (Goodset φ.toLinearMap) = 
    {v : {v : Fin r → E // LinearIndependent 𝕜 v} | LinearIndependent 𝕜 (φ ∘ v.1)} := by
    ext v 
    simp only [Set.mem_preimage, mk'_eq_mk, Set.mem_setOf_eq] 
    exact GoodsetPreimage φ.toLinearMap v.2
  rw [heq]
  exact GoodsetIsOpen_aux2 φ


noncomputable def ContChart (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) : Grassmannian 𝕜 E r → ((Fin r → 𝕜) →L[𝕜] U) := 
fun W => ContinuousLinearMap.mk (Chart φ.toLinearEquiv W) (LinearMap.continuous_of_finiteDimensional _)

/- To prove that the chart is continuous, we lift it to (Fin r → E) and we prove that the lift is smooth.-/

def ContChartLift (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) : (Fin r → E) → ((Fin r → 𝕜) →L[𝕜] U) := 
fun v => ContinuousLinearMap.mk (ChartLift φ.toLinearEquiv v) (LinearMap.continuous_of_finiteDimensional _)
  

lemma ContChartLift_isLift (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) {v : Fin r → E} (hv : LinearIndependent 𝕜 v) :
ContChart φ (Grassmannian.mk 𝕜 v hv) = ContChartLift φ v := by 
  unfold ContChart ContChartLift
  simp only [ContinuousLinearMap.mk.injEq]
  apply ChartLift_isLift

variable (𝕜 E r)


def ChartLiftHelper1 : (Fin r → E) →ₗ[𝕜] ((Fin r → 𝕜) →L[𝕜] E) :=
{
  toFun := fun v => (Basis.constrL (Pi.basisFun 𝕜 (Fin r)) v)  
  map_add' := by intro v w; simp only
                 apply ContinuousLinearMap.coe_injective
                 rw [ContinuousLinearMap.coe_add,Basis.coe_constrL, Basis.coe_constrL, Basis.coe_constrL]
                 simp only [map_add]
  map_smul' := by intro a v; simp only
                  apply ContinuousLinearMap.coe_injective
                  rw [ContinuousLinearMap.coe_smul, Basis.coe_constrL, Basis.coe_constrL]
                  simp only [map_smul, RingHom.id_apply]
}

lemma ChartLiftHelper1_norm_le (v : Fin r → E) : ‖ChartLiftHelper1 𝕜 E r v‖ ≤ r * ‖v‖ := by
  apply ContinuousLinearMap.op_norm_le_bound _ (mul_nonneg (Nat.cast_nonneg r) (norm_nonneg v))
  intro a 
  unfold ChartLiftHelper1
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Basis.constrL_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply] 
  refine le_trans (norm_sum_le (ι := Fin r) ⊤ (fun i => a i • v i)) ?_
  have hav : ∀ (i : Fin r), ‖a i • v i‖ ≤ ‖v‖ * ‖a‖ := by
    intro i
    rw [norm_smul, mul_comm]
    apply mul_le_mul (norm_le_pi_norm _ i) (norm_le_pi_norm _ i) (norm_nonneg _) (norm_nonneg _)
  refine le_trans (Finset.sum_le_card_nsmul ⊤ _ (‖v‖ * ‖a‖) (fun i _ => hav i)) ?_
  simp only [Finset.top_eq_univ, Finset.card_fin, nsmul_eq_mul]
  rw [mul_assoc]

def ChartLiftHelper1L :  (Fin r → E) →L[𝕜] ((Fin r → 𝕜) →L[𝕜] E) :=
LinearMap.mkContinuous (ChartLiftHelper1 𝕜 E r) r (ChartLiftHelper1_norm_le 𝕜 E r)

def ChartLiftHelper2 (φ : E →L[𝕜] (Fin r → 𝕜)) : (Fin r → E) →L[𝕜] (Fin r → 𝕜) →L[𝕜] (Fin r → 𝕜) :=
ContinuousLinearMap.comp (ContinuousLinearMap.compL 𝕜 (Fin r → 𝕜) E (Fin r → 𝕜) φ) (ChartLiftHelper1L 𝕜 E r)

variable {r}

def ChartLiftHelper3 (F G : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] : 
(F →L[𝕜] G) × (E →L[𝕜] F) → (E →L[𝕜] G) := fun x => ContinuousLinearMap.compL 𝕜 _ _ _ x.1 x.2

def IsBoundedBilinearMap_chartLiftHelper3 (F G : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] 
[NormedAddCommGroup G] [NormedSpace 𝕜 G] : IsBoundedBilinearMap 𝕜 (ChartLiftHelper3 𝕜 E F G) := by
  apply ContinuousLinearMap.isBoundedBilinearMap 

variable {𝕜 E}


lemma ContChartLift_eq (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) (v : Fin r → E):
ContChartLift φ v = ContinuousLinearMap.compL 𝕜 (Fin r → 𝕜) E U
    ((ContinuousLinearMap.snd 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) 
    (ChartLiftHelper3 𝕜 (Fin r → 𝕜) (Fin r → 𝕜) E ⟨(ChartLiftHelper1L 𝕜 E r v), 
    (Ring.inverse (ChartLiftHelper2 𝕜 E r ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) v))⟩) := sorry 
 

lemma ChartLiftSmoothOn (φ : E ≃L[𝕜] (Fin r → 𝕜) × U) : ContDiffOn 𝕜 ⊤ (ContChartLift φ) 
{v | LinearIndependent 𝕜 (φ ∘ v)} := by
  refine ContDiffOn.congr ?_ (fun v _ => ContChartLift_eq φ v)
  apply ContDiffOn.continuousLinearMap_comp    
  have heq : ∀ v, (ChartLiftHelper3 𝕜 (Fin r → 𝕜) (Fin r → 𝕜) E ⟨(ChartLiftHelper1L 𝕜 E r v), 
    (Ring.inverse (ChartLiftHelper2 𝕜 E r ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) v))⟩) = 
    ((ChartLiftHelper3 𝕜 (Fin r → 𝕜) (Fin r → 𝕜) E) ∘ (fun v => ⟨(ChartLiftHelper1L 𝕜 E r v), 
    (Ring.inverse (ChartLiftHelper2 𝕜 E r ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) v))⟩)
    ) v := sorry 
  refine ContDiffOn.congr ?_ (fun v _ => heq v)
  apply ContDiff.comp_contDiffOn (IsBoundedBilinearMap.contDiff (IsBoundedBilinearMap_chartLiftHelper3 _ _ _ _))
  apply ContDiffOn.prod
  . apply ContDiff.contDiffOn
    apply ContinuousLinearMap.contDiff 
  . 


#exit   
  refine ContDiffOn.congr ?_ (fun v _ => ContChartLift_eq φ v)
  apply ContDiffOn.continuousLinearMap_comp    
  sorry 



end Grassmannian
end Topology



#exit 


class MySpecialEquiv (𝕜 E U : Type*) [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup U] [Module 𝕜 U] (r : ℕ) :=
  (myEquiv : E ≃ₗ[𝕜] (Fin r → 𝕜) × U)

variable {ε : MySpecialEquiv 𝕜 E U r}

end 

