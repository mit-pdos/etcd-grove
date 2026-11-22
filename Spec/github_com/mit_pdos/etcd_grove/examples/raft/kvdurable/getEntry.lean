/- Lean-first (no Rocq counterpart).

`getEntry(b)` (storage.go): what `putEntry` wrote at the start of `b` (`encEntry e`, of a known
type, `EntWf`), read back into a fresh entry (`entOwn`: its fields owned, its cells and data
read-only), the rest, and `ok`. The bytes are held at any fraction `dq`, the rest given back at it;
the entry's data, a slice of `b`, is made read-only for good (a log entry's data is read-only,
`entPts`), so that part of `b` is not given back (ledger 2026-11-21: until then the bytes were
persistent, `↦*□`). Stated of bytes `putEntry` wrote, so `ok` is `true`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Codec
public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Assumptions]

/-- See the file header. -/
abbrev getEntry.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (e : EntryM) (r : List w8),
  EntWf e →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable ∗ b ↦*{dq} (encEntry e ++ r) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.getEntry)) (Val #b))
  {{ (l : Loc) (rest : GoSlice), RET (PairV (PairV #l #rest) #true);
      entOwn l e ∗ rest ↦*{dq} r }}

end spec

end raft_kvdurable
end EtcdGrove
end Perennial
