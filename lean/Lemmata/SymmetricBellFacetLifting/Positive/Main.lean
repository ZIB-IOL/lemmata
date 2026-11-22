module

public import Lemmata.SymmetricBellFacetLifting.Positive.Hull
public import Lemmata.SymmetricBellFacetLifting.Positive.Case2
public import Lemmata.SymmetricBellFacetLifting.Positive.Case3
public import Lemmata.SymmetricBellFacetLifting.Positive.Case4
public import Lemmata.SymmetricBellFacetLifting.Positive.Case5

@[expose] public section
namespace Lemmata.SymmetricBellFacetLifting.Positive

/-- Real convex-hull equality in the normalized, invertible chart for (3,2). -/
theorem positive_2 : convexHull ℝ (chartAtoms 2 1 4 inv2) = unitCross 1 :=
  hull_of_integer_certificate (by decide) (by decide)
    (fun _ ha _ hb _ hc => all_rows_2 ha hb hc) (fun _ hv => signed_axes_2 hv)

/-- Real convex-hull equality in the normalized, invertible chart for (3,3). -/
theorem positive_3 : convexHull ℝ (chartAtoms 3 2 144 inv3) = unitCross 2 :=
  hull_of_integer_certificate (by decide) (by decide)
    (fun _ ha _ hb _ hc => all_rows_3 ha hb hc) (fun _ hv => signed_axes_3 hv)

/-- Real convex-hull equality in the normalized, invertible chart for (3,4). -/
theorem positive_4 : convexHull ℝ (chartAtoms 4 2 96 inv4) = unitCross 2 :=
  hull_of_integer_certificate (by decide) (by decide)
    (fun _ ha _ hb _ hc => all_rows_4 ha hb hc) (fun _ hv => signed_axes_4 hv)

/-- Real convex-hull equality in the normalized, invertible chart for (3,5). -/
theorem positive_5 : convexHull ℝ (chartAtoms 5 3 3200 inv5) = unitCross 3 :=
  hull_of_integer_certificate (by decide) (by decide)
    (fun _ ha _ hb _ hc => all_rows_5 ha hb hc) (fun _ hv => signed_axes_5 hv)

end Lemmata.SymmetricBellFacetLifting.Positive
