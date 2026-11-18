/-
The pure theory of the key index (`Model.lean`): what `kiGet` answers after `kiPut` and
`kiTombstone`, under the well-formedness `KiWf` the code maintains. Lean-first.

**`KiWf ki`**: the generations are not empty as a list, every generation but the last has a
revision, each generation's `created` is its first revision and its `ver` its number of
revisions. Together with "the new revision is above every revision of `ki`" (`KiAbove`), this
is what the lemmas below need:

- `kiGet_kiPut_below`, `kiGet_kiTombstone_below`: a read strictly below the new revision's
  main is unchanged;
- `kiGet_kiPut_above`: a read at or above it sees the new revision, with the last generation's
  create revision (the new revision's if it was empty) and version + 1;
- `kiGet_kiTombstone_above`: a read at or above a tombstone sees nothing;
- `kiGet_top`: a read at or above every revision sees the last generation's last revision, or
  nothing if it is empty.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ### Generations after a put -/

/-! ### List helpers: the last element replaced -/

/-! ### The scan, looking only at the generations it visits -/

/-! ### The walk after an appended revision -/

/-! ### Facts about a well-formed key index -/

/-! ### The scan after a put -/

/-! ### The generation's answer, and a put seen from below -/

/-! ### The scan after a tombstone -/

/-! ### Well-formedness and the revisions, through a put and a tombstone -/

/-! ### The empty key index -/

/-- A key index with one empty generation: what `kiPut` starts from when there is none, and
what a tombstone leaves behind. -/
def kiEmpty : KeyIndex := { modified := Rev.zero, gens := [Gen.empty] }

end mvcc
end EtcdGrove
end Perennial
