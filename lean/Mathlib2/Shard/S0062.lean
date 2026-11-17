/- Mathlib2 分片 62（forge 自动维护，追加式）。 -/
import Mathlib
import Mathlib2.Shard.S0052
import Mathlib2.Shard.S0059
set_option maxHeartbeats 400000
namespace Mathlib2

-- forge:entry x2611_15210_thm1_2_s1h2 kind=proved origin=decomposition
section
/- x2611_15210_thm1_2 的证明骨架中第 2 个空洞 -/
theorem x2611_15210_thm1_2_s1h2 :
    ∀ (m : ℕ), 3 ≤ m → Odd m → x2611_15210_rho 3 ≤ x2611_15210_rho m := by
  intro m hm _
  exact x2611_15210_thm4_2_aux5 m hm
end

end Mathlib2
