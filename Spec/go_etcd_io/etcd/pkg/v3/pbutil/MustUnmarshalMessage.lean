/-
`pbutil.MustUnmarshalMessage(um, data)` (`pkg/v3/pbutil`, names-only), on a raft
`ConfChange`: the trust boundary. Lean-first (no Rocq counterpart); see `InvRaftpb.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3 go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `MustUnmarshalMessage(&cc, data)` unmarshals the bytes `bs` of a committed conf-change
entry, the encoding of a `ConfChange` (`isConfChangeEncoding`: its proposer marshalled it), into
`cc`: `cc` holds some change, whose `Id` field holds some id. (On other bytes it panics: the
premise is the caller's, `entriesFrom`.) -/
abbrev pbutil.MustUnmarshalMessage.spec : Prop :=
  ∀ (cc : Loc) (v : raftpb.ConfChange) (d : GoSlice) (bs : List w8) (dq : DFrac),
  isConfChangeEncoding bs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗ cc ↦ v ∗ d ↦*{dq} bs }}
    (App (App (Val (@! pbutil.MustUnmarshalMessage))
      (Val #(interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #cc))) (Val #d))
  {{ RET #(); (∃ (v' : raftpb.ConfChange) (id : w64), cc ↦ v' ∗ optU64 v'.Id' id) ∗
      d ↦*{dq} bs }}

end spec

end EtcdGrove
end Perennial
