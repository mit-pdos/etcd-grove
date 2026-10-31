/-
`apply.applierV3backend.Compaction` (backend.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/CompactArm.lean` (M2, the apply side, item 10).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.CompactArm

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.Compaction(cr)`** on the `*applierV3backend` `p`: `EnsureTrace` makes a fresh trace
(`context.TODO()` holds none), `KV.Compact(trace, rev)` (the watchable store's embedded `*store`'s,
`store.Compact.spec`: the right, the certificate of a log with `rev`, the hook, the contract, the
reader's token, the supply), then, on success, `KV.Range(context.TODO(), "compaction", nil, {})`
(its result not `nil`: the context is never done) for the response's header. The chain-`.backend`
instance of the chain's `Compaction` triple. -/
abbrev apply.applierV3backend.Compaction.spec : Prop :=
  ∀ (E : AEnv GF) (p cr : Loc) (rev : w64) (log : mvcc.Log) (crev : Int) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.backendIs E p ∗ apply.compactionIs cr rev ∗ ⌜apply.cmpAdmitRev E.γ.kb log rev⌝ ∗
      apply.mPre E .backend (interface.mkOk (go.GoType.PointerType applierV3backend.ty) #p) info log
        Pre Q Post ∗ apply.cmpOwn E crev }}
    (App (Val (p @!! go.GoType.PointerType applierV3backend.ty @!! go!"Compaction")) (Val #cr))
  {{ (resp : Loc) (ch : GoChan) (trace : Loc) (err : GoInterface),
      RET (PairV (PairV (PairV #resp #ch) #trace) #err);
      apply.kvOwn E log ∗ (Post ∨ Pre) ∗ apply.cmpOwn E (apply.cmpRevAfter crev rev) ∗
      apply.cmpAnswerIs .backend crev rev resp ch trace err }}

end spec

end EtcdGrove
end Perennial
