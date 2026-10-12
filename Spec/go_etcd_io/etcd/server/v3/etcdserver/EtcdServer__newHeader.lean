/-
`s.newHeader()` (`v3_server.go`): a fresh response header of the cluster, the member, the KV's revision, the term and the leader.
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.newHeader()`: a fresh `*pb.ResponseHeader` (owned) with the member's id `mid` and the
KV's revision (`store.Rev`: the last revision of a certified log), some cluster id, term and
leader; a reader's slots of the store. -/
abbrev EtcdServer.newHeader.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (cl : Loc) (mid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerRead s E γr ∗ srvClusterAddr s ↦□ cl ∗ srvMemberIDAddr s ↦□ mid ∗ srvLeadInv s ∗
      mvcc.storeReader E.s E.γ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"newHeader")) (Val #()))
  {{ (h : Loc), RET #h; mvcc.storeReader E.s E.γ ∗
      ∃ (v : etcdserverpb.ResponseHeader) (log : mvcc.Log), h ↦ v ∗ mvcc.idxCert E.γ.idx log ∗
        ⌜log ≠ [] ∧ v.MemberId' = mid ∧ v.Revision' = W64 ((log.length : Int) - 1)⌝ }}

end spec

end EtcdGrove
end Perennial
