/-
`EnsureSnapshot` (`raftpb/util.go:57`, new in raft v3.7). Lean-first (raft v3.7 retarget,
stage R1).
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `EnsureSnapshot(s)` of a snapshot pointer, `nil` (`none`) or owned (fully) holding a snapshot:
a non-`nil` snapshot holding the same record (the zero record for `nil`), owned; `s` itself when
`s` was not `nil`. -/
abbrev raftpb.EnsureSnapshot.spec : Prop :=
  ∀ (s : Loc) (o : Option SnapshotM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ snapOpt s (DFrac.own 1) o }}
    (App (Val #(functions raftpb.EnsureSnapshot [])) (Val #s))
  {{ (r : Loc), RET #r;
      ownSnapM r (DFrac.own 1) (o.getD (SnapshotM.mk [] (SnapshotMetadataM.mk
        (ConfStateM.mk [] [] [] [] false) (W64 0) (W64 0)))) ∗ ⌜s ≠ null → r = s⌝ }}

end spec

end EtcdGrove
end Perennial
