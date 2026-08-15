import HalfOne.Fast
namespace HalfOne
set_option maxRecDepth 4000000
set_option maxHeartbeats 0
theorem c4 : (Finset.univ.filter (fun G : HGraph 4 => goodB G)).card = 5 := by
  rw [census_eq_fast]; decide +kernel
theorem c5 : (Finset.univ.filter (fun G : HGraph 5 => goodB G)).card = 168 := by
  rw [census_eq_fast]; decide +kernel
end HalfOne
