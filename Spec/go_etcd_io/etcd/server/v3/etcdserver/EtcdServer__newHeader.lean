/-
`s.newHeader()` (`v3_server.go`): a fresh response header of the cluster, the member, the KV's revision, the term and the leader.
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.newHeader()`: a fresh `*pb.ResponseHeader` (owned) with the member's id `mid` and the
KV's revision (`store.Rev`: the last revision of a certified log), the cluster's id `cid`
(`c.cid`, read-only: `membership.clusterCid`, unit P1b), some term and leader; a reader's slots
of the store; in either auth mode `on` (the lease-read plan, 2026-10-31: `isServerReadM`, until
then `isServerRead`, the mode off's). (Strict M1, 2026-11-06: the draft's `newHeaderPostA`, with
the witness `E.Nx` (`kvNx γr on` by the KV invariants' tie, as `rangeReadOkM`): the thread's token in
place of the store's reader slot, the log read a floor `kvLogLb`, with its witness, its receipt and
`LogWf'`.) -/
abbrev EtcdServer.newHeader.spec : Prop :=
  ∀ (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (cl : Loc) (mid cid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReadM on s E γr ∗ srvClusterAddr s ↦□ cl ∗ membership.clusterCid cl cid ∗
      srvMemberIDAddr s ↦□ mid ∗ srvLeadInv s ∗
      threadTok }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"newHeader")) (Val #()))
  {{ (h : Loc), RET #h; threadTok ∗
      ∃ (v : etcdserverpb.ResponseHeader) (log : mvcc.Log), h ↦ v ∗ srvApi.kvLogLb E.γs log ∗
        E.Nx log ∗ ⧖ (mvcc.logCh log) ∗
        ⌜mvcc.LogWf' log ∧ log ≠ [] ∧ v.ClusterId' = cid ∧ v.MemberId' = mid ∧
          v.Revision' = W64 ((log.length : Int) - 1)⌝ }}

end spec

end EtcdGrove
end Perennial
