import Gleason.Harmonic.Sphere.SphereFrameQ02
import Gleason.Harmonic.Auxiliary.QuadraticSubmodule

noncomputable section

theorem sphereFrameSubmodule_eq_sup_zero_two_of_independent_sector_decomposition
    (hQind : iSupIndep harmonicSphereDegreeSubmodule)
    (hQnontriv : ∀ n, harmonicSphereDegreeSubmodule n ≠ ⊥)
    {s : Set ℕ}
    (hF : sphereFrameSubmodule = ⨆ i : s, harmonicSphereDegreeSubmodule i)
    (hQ0 : harmonicSphereDegreeSubmodule 0 ≤ sphereFrameSubmodule)
    (hQ2 : harmonicSphereDegreeSubmodule 2 ≤ sphereFrameSubmodule) :
    sphereFrameSubmodule = harmonicSphereDegreeSubmodule 0 ⊔ harmonicSphereDegreeSubmodule 2 := by
  refine eq_sup_zero_two_of_independent_sector_decomposition
    (Q := harmonicSphereDegreeSubmodule) hQind hQnontriv hF hQ0 hQ2 ?_ ?_
  · exact not_harmonicSphereDegreeSubmodule_one_le_sphereFrameSubmodule
  · intro n hn
    exact not_harmonicSphereDegreeSubmodule_gt_two_le_sphereFrameSubmodule hn

theorem sphereFrameSubmodule_le_sphereQuadraticSubmodule_of_independent_sector_decomposition
    (hQind : iSupIndep harmonicSphereDegreeSubmodule)
    (hQnontriv : ∀ n, harmonicSphereDegreeSubmodule n ≠ ⊥)
    {s : Set ℕ}
    (hF : sphereFrameSubmodule = ⨆ i : s, harmonicSphereDegreeSubmodule i)
    (hQ0 : harmonicSphereDegreeSubmodule 0 ≤ sphereFrameSubmodule)
    (hQ2 : harmonicSphereDegreeSubmodule 2 ≤ sphereFrameSubmodule) :
    sphereFrameSubmodule ≤ sphereQuadraticSubmodule := by
  apply eq_sup_zero_two_imp_le_sphereQuadraticSubmodule
  exact sphereFrameSubmodule_eq_sup_zero_two_of_independent_sector_decomposition
    hQind hQnontriv hF hQ0 hQ2

theorem sphereFrameSubmodule_eq_sup_zero_two_of_sector_decomposition
    (hQind : iSupIndep harmonicSphereDegreeSubmodule)
    (hQnontriv : ∀ n, harmonicSphereDegreeSubmodule n ≠ ⊥)
    {s : Set ℕ}
    (hF : sphereFrameSubmodule = ⨆ i : s, harmonicSphereDegreeSubmodule i) :
    sphereFrameSubmodule = harmonicSphereDegreeSubmodule 0 ⊔ harmonicSphereDegreeSubmodule 2 := by
  exact sphereFrameSubmodule_eq_sup_zero_two_of_independent_sector_decomposition
    hQind hQnontriv hF
    harmonicSphereDegreeSubmodule_zero_le_sphereFrameSubmodule
    harmonicSphereDegreeSubmodule_two_le_sphereFrameSubmodule

theorem sphereFrameSubmodule_le_sphereQuadraticSubmodule_of_sector_decomposition
    (hQind : iSupIndep harmonicSphereDegreeSubmodule)
    (hQnontriv : ∀ n, harmonicSphereDegreeSubmodule n ≠ ⊥)
    {s : Set ℕ}
    (hF : sphereFrameSubmodule = ⨆ i : s, harmonicSphereDegreeSubmodule i) :
    sphereFrameSubmodule ≤ sphereQuadraticSubmodule := by
  apply eq_sup_zero_two_imp_le_sphereQuadraticSubmodule
  exact sphereFrameSubmodule_eq_sup_zero_two_of_sector_decomposition hQind hQnontriv hF
