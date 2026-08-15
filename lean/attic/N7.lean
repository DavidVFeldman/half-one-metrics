import HalfOne.Fast
namespace HalfOne
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
theorem c7 : (Finset.univ.filter (fun G : HGraph 7 => goodB G)).card = 1309868 := by
  rw [census_eq_fast]; native_decide
end HalfOne
