import FavardLength.BasicProof.Cantor
import FavardLength.BasicProof.ProjLength
import FavardLength.BasicProof.Favard
import FavardLength.BasicProof.Energy

/-!
# Proofs of the basic lemmas

Imports every file of `FavardLength/BasicProof/`. For each lemma `X` stated in
`FavardLength/Basic.lean`, the theorem `Favard.BasicProof.X` has the identical statement, proved
without importing `FavardLength.Basic`:

* `FavardLength.BasicProof.Cantor`: sanity checks, square decomposition, nesting, compactness,
  reflection symmetry of `C_n`, projections of squares;
* `FavardLength.BasicProof.ProjLength`: finiteness, the `√2` bound, monotonicity,
  measurability, and symmetries of the projection length;
* `FavardLength.BasicProof.Favard`: the symmetry reduction of the Favard integral and its bounds;
* `FavardLength.BasicProof.Energy`: multiplicity, total mass, and the overlap formula for the
  energy.
-/
