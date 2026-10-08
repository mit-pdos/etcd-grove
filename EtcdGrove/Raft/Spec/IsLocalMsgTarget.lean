/-
Port of election_proof/spec_IsLocalMsgTarget.v (feb5c73d4).
-/
import EtcdGrove.Raft.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `id` is one of the two reserved local targets, `LocalAppendThread = MaxUint64` and
`LocalApplyThread = MaxUint64 - 1`. -/
abbrev IsLocalMsgTarget.spec : Prop :=
  ∀ (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions IsLocalMsgTarget [])) (Val #id))
  {{ RET #(decide (id = W64 18446744073709551615 ∨ id = W64 18446744073709551614)); True }}

end spec

end EtcdGrove
end Perennial
