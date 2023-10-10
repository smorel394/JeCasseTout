import Mathlib.Tactic
import JeCasseTout.TopCharts
import JeCasseTout.SeparatingMaps 

variable {𝕜 E U : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] 
[NormedAddCommGroup U] [NormedSpace 𝕜 U] [CompleteSpace 𝕜] {r : ℕ}




#exit
class MySpecialEquiv (𝕜 E U : Type*) [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup U] [Module 𝕜 U] (r : ℕ) :=
  (myEquiv : E ≃ₗ[𝕜] (Fin r → 𝕜) × U)

variable {ε : MySpecialEquiv 𝕜 E U r}

end 