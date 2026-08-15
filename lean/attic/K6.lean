import HalfOne.Fast
namespace HalfOne
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
theorem c6 : (Finset.univ.filter (fun G : HGraph 6 => goodB G)).card = 12326 := by
  rw [census_eq_fast]; decide +kernel
end HalfOne
