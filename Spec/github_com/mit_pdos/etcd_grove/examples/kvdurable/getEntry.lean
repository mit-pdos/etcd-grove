/- Lean-first (no Rocq counterpart).

`getEntry(b)` (storage.go): what `putEntry` wrote at the start of `b` (`encEntry e`, of a known
type, `EntWf`), read back into a fresh entry (`entOwn`: its fields owned, its cells and data
read-only), the rest, and `ok`. The bytes are read-only for good (`↦*□`): the entry's data is a
slice of `b`, and a log entry's data is read-only (`entPts`). Stated of bytes `putEntry` wrote, so
`ok` is `true`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Codec
public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

/-- See the file header. -/
abbrev getEntry.spec : Prop :=
  ∀ (b : GoSlice) (e : EntryM) (r : List w8),
  EntWf e →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ b ↦*□ (encEntry e ++ r) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.getEntry)) (Val #b))
  {{ (l : Loc) (rest : GoSlice), RET (PairV (PairV #l #rest) #true);
      entOwn l e ∗ rest ↦*□ r }}

end spec

end kvdurable
end EtcdGrove
end Perennial
