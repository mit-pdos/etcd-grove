/-
`lease.newLessor(lg, b, cluster, cfg)` (`lessor.go:212-249`): the `*lessor` `NewLessor` wraps in the
`Lessor` interface. Lean-first (no Rocq counterpart); prove-ps2-newlessor5, 2026-11-21: what retires
`NewLessor`'s axiom (`NewLessor.lean` is `newLessor`'s statement at the interface).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Recover

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`newLessor(lg, b, cl, cfg)`**: `NewLessor.spec` at the `*lessor` `lp` it returns (`NewLessor`
converts it to the `Lessor` interface, `lessorIface lp`); why each clause is true of the Go code is in
`NewLessor.spec`'s docstring. -/
abbrev lease.newLessor.spec : Prop :=
  ∀ (lg : Loc) (cl : GoInterface) (cfg : go_etcd_io.etcd.server.v3.lease.LessorConfig)
    (d : mvcc.KBReal) (W Pk : IProp GF) (qo : Qp) (GA : w64 → IProp GF)
    (S : GoString → Prop) (r : GMap GoString backend.BktData) (mono : Bool)
    (recs : List (w64 × w64 × w64)) (reqOf : w64 → w64) (Lr : List w64),
  S go!"lease" → mvcc.leaseParams d.P →
  backend.bktEnts ((r.lookup go!"lease").getD ∅) = recs.map lease.leaseRecEnc →
  (∀ x ∈ recs, sint.Z (reqOf x.1) ≤ sint.Z x.2.1) → Lr.Perm (recs.map (·.1)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      (⌜lg = null⌝ ∨ zapLoggerOk lg) ∗
      ⌜0 ≤ sint.Z cfg.leaseRevokeRate'⌝ ∗ lease.clusterOk cl ∗
      backend.isBackend d.γB d.P W Pk d.be ∗ backend.bOpen d.γB qo ∗ ownToks d.γB.wb 2 ∗
      backend.rbPart d.γB S r ∗ □ ([∗list] id ∈ recs.map (·.1), GA id) ∗
      ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.newLessor)) (Val #lg))
      (Val #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #d.be)))
      (Val #cl)) (Val #cfg))
  {{ (lp : Loc), RET #lp; backend.bOpen d.γB qo ∗
      backend.rbOwnIn d.γB S (r.insert go!"lease" ((r.lookup go!"lease").getD ∅)) ∗
      ∃ γl : GName, lease.lessorInv lp γl ∗ lease.lessorModeIs γl mono ∗
      lease.lessorCfg lp ∗ lease.lF go!"minLeaseTTL" lp ↦□ cfg.MinLeaseTTL' ∗
      lease.lessorExpiredC lp GA ∗ lease.lessorGuard γl GA ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - 1) (), lease.lessorRdOf γl) ∗
      lease.leaseOwn γl Lr ∅ ∗ lease.lessorWinTie γl [] ∗ lease.leaseEver γl (recs.map (·.1)) ∗
      lease.leaseRevokers γl Lr ∗
      lease.rdOwn γl func.nil ∗
      lease.lessorBeOn lp d.be ∗ lessorApplyOk lp ∗
      lease.lessorStopTok lp ∗
      □ ([∗list] x ∈ recs, lease.leaseReqIs γl x.1 (reqOf x.1)) ∗
      (∃ ls : List Loc, ⌜ls.length = recs.length⌝ ∗
        lease.lessorAt γl 0 (lease.recMap (recs.zip ls), ∅, lease.recTTLs cfg.MinLeaseTTL' recs)) }}

end spec

end EtcdGrove
end Perennial
