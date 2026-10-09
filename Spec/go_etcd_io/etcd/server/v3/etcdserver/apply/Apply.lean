/-
`apply.Apply(lg, e, uberApply, w, shouldApplyV3)` (`server/v3/etcdserver/apply/apply.go`):
the trust boundary for what the applier writes. Lean-first (no Rocq counterpart); see
`InvApplier.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The applier's contract.** `apply.Apply(lg, e, ua, w, v3)` unmarshals the entry `e`'s
request and, if it must (a waiter or side effects), applies it through the `UberApplier`
`ua`, whose backend's batch lock has invariant `P` and runs the post-lock hook `f`
(`applierFor`). For `v3` (`ApplyBoth`) the entry's writes to the backend happen in **one**
critical section of the batch lock (`LockInsideApply` ... `Unlock`), or not at all: in the
first case the applier takes the lock (`P`), runs the hook (its triple, from the caller:
`{P ∗ Pre} f() {Q}`), writes (the caller's update `Q ={⊤}=∗ P ∗ Post`, which models the
writes) and unlocks; in the second it writes nothing, and the caller keeps `Pre`. Without
`v3` (`ApplyV2storeOnly`: an entry already in the backend, replayed) it writes nothing to
the backend. It returns a result (`nil`, or one whose `Err` can be read) and the request's
id. -/
abbrev apply.Apply.spec : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (P Pre Q Post : IProp GF)
    (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      applierFor ua P f ∗ entryAt e m ∗
      (if v3 then iprop(□ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
          (Q ={⊤}=∗ P ∗ Post))
       else iprop(True)) ∗ Pre }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id : w64), RET (PairV #ar #id);
      (if v3 then iprop(Post ∨ Pre) else Pre) ∗ resultOk ar }}

end spec

end EtcdGrove
end Perennial
