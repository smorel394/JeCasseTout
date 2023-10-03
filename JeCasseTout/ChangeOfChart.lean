import Mathlib.Tactic
import JeCasseTout.TopCharts


noncomputable section 


namespace Grassmannian

/- Note: if my changes to mathlib are accepted, change the NontriviallyNormedField 𝕜 to 
NontriviallyNormedDivisionRing 𝕜 We will also need to introduce a NontriviallyNormedField over which
𝕜 is an algebra and E and U are NormedSpaces.-/
/-variable {𝕜 E U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [BoundedSMul 𝕜 E]
[NormedAddCommGroup U] [Module 𝕜 U] [BoundedSMul 𝕜 U] [CompleteSpace 𝕜] {r : ℕ}-/

variable {𝕜 E U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace 𝕜] {r : ℕ}

def ChangeOfChart (φ ψ : E ≃L[𝕜] (Fin r → 𝕜) × U) : ((Fin r → 𝕜) →L[𝕜] U) → ((Fin r → 𝕜) →L[𝕜] U) :=
(Chart φ) ∘ (InverseChart ψ)

lemma ChangeOfChartDomain (φ ψ : E ≃L[𝕜] (Fin r → 𝕜) × U) : (LocalHomeomorph.trans (LocalHomeomorph.symm 
(Chart_LocalHomeomorph ψ)) (Chart_LocalHomeomorph φ)).toLocalEquiv.source = 
{f : ((Fin r → 𝕜) →L[𝕜] U) | Submodule.map ψ.symm (LinearMap.graph f) ⊓ 
LinearMap.ker ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) = ⊥} := by
  ext f 
  simp only [LocalHomeomorph.trans_toLocalEquiv, LocalHomeomorph.symm_toLocalEquiv, LocalEquiv.trans_source,
    LocalEquiv.symm_source, LocalHomeomorph.coe_coe_symm, Set.mem_inter_iff, Set.mem_preimage, ge_iff_le,
    Set.mem_setOf_eq]
  unfold Chart_LocalHomeomorph Chart_LocalEquiv
  simp only [Set.top_eq_univ, Set.mem_univ, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_fst,
    LocalHomeomorph.mk_coe_symm, LocalEquiv.coe_symm_mk, true_and, ge_iff_le]
  unfold InverseChart Goodset
  simp only [ge_iff_le, Set.mem_setOf_eq]
  rfl

lemma ChangeOfChartSmooth (φ ψ : E ≃L[𝕜] (Fin r → 𝕜) × U) :
ContDiffOn 𝕜 ⊤ (ChangeOfChart φ ψ) {f : ((Fin r → 𝕜) →L[𝕜] U) | Submodule.map ψ.symm (LinearMap.graph f) ⊓ 
LinearMap.ker ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) = ⊥} := by 
  have heq : ChangeOfChart φ ψ = (ChartLift φ) ∘ (InverseChartLift ψ) := by
    ext f 
    unfold ChangeOfChart
    simp only [Function.comp_apply]
    rw [InverseChartLift_isLift, ChartLift_isLift]
  rw [heq]
  have hdom : {f : ((Fin r → 𝕜) →L[𝕜] U) | Submodule.map ψ.symm (LinearMap.graph f) ⊓ 
    LinearMap.ker ((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) = ⊥} = ⊤ ∩
    (InverseChartLift ψ)⁻¹'  {v : Fin r → E | LinearIndependent 𝕜 
    (((ContinuousLinearMap.fst 𝕜 (Fin r → 𝕜) U).comp φ.toContinuousLinearMap) ∘ v)} := by
    ext f
    simp only [ge_iff_le, Set.mem_setOf_eq, Set.top_eq_univ, ContinuousLinearMap.coe_comp',
      ContinuousLinearMap.coe_fst', ContinuousLinearEquiv.coe_coe, Set.preimage_setOf_eq, Set.univ_inter]
    unfold InverseChartLift
    simp only [ge_iff_le, Pi.basisFun_apply]
    sorry
  rw [hdom]
  apply ContDiffOn.comp' (f := InverseChartLift ψ) (g := ChartLift φ) (s := ⊤) 
  . exact ChartLiftSmoothOn φ
  . apply ContDiff.contDiffOn
    exact InverseChartLiftSmooth ψ

end Grassmannian

end 


#exit 


class MySpecialEquiv (𝕜 E U : Type*) [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup U] [Module 𝕜 U] (r : ℕ) :=
  (myEquiv : E ≃ₗ[𝕜] (Fin r → 𝕜) × U)

variable {ε : MySpecialEquiv 𝕜 E U r}

end 
