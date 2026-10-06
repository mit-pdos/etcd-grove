/-
Port of `election_proof/spec_raftLog__appliedTo.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

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

/-- `l.appliedTo(i, size)` advances `applied` to `i`. It `Panicf`s unless
`applied ≤ i ≤ committed`, hence the premise; the `applying*` fields it also writes are
not part of `LogState`. -/
abbrev raftLog.appliedTo.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i size : w64),
  uint.Z ls.applied ≤ uint.Z i ∧ uint.Z i ≤ uint.Z ls.committed →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftLog l ls }}
    (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"appliedTo")) (Val #i))
      (Val #size))
  {{ RET #(); ownRaftLog l { ls with applied := i } }}

end spec

end EtcdGrove
end Perennial
