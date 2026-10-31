/- Lean-first (no Rocq counterpart).

`putEntry(buf, e)` (storage.go): `buf` with the entry at `l` appended (`encEntry`: its term, index
and type, then its data), the entry only read (at any fraction: a log entry is read-only,
`entRO`).
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
abbrev putEntry.spec : Prop :=
  ∀ (buf : GoSlice) (B : List w8) (l : Loc) (dq : DFrac) (e : EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ buf ↦* B ∗ ownSliceCap w8 buf (DFrac.own 1) ∗ entPts l dq e }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.putEntry)) (Val #buf)) (Val #l))
  {{ (s : GoSlice), RET #s; s ↦* (B ++ encEntry e) ∗ ownSliceCap w8 s (DFrac.own 1) ∗
      entPts l dq e }}

end spec

end kvdurable
end EtcdGrove
end Perennial
