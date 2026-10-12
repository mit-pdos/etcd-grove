/-
`apply.Apply` (apply.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/InvUber.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The applier's contract, with what an entry does to the KV.** `apply.Apply(lg, e, ua, w, v3)`
decodes the entry `e`'s request `rq` (the premise: its data decode, `irrDecode`), computes its id
(`irrId rq = some id`: an id, or a header's) and, if it must (a waiter, `w.IsRegistered(id)`, or
side effects, `noSideEffect`), applies it through the `UberApplier` `ua` (`applierFor ua E`), whose
backend's batch lock has invariant `E.P` and runs the post-lock hook `E.f`.
* **The server's protocol** (as before unit 2): for `v3` (`ApplyBoth`) the entry's writes to the
  backend happen in **one** critical section of the batch lock (`LockInsideApply` ... `Unlock`),
  or not at all: in the first case the applier takes the lock (`E.P`), runs the hook (its triple,
  from the caller: `{E.P ∗ Pre} E.f() {Q}`), writes (the caller's update `Q ={⊤}=∗ E.P ∗ Post`,
  which models the writes) and unlocks; in the second it writes nothing, and the caller keeps
  `Pre`. Without `v3` (`ApplyV2storeOnly`: an entry already in the backend, replayed) it writes
  nothing to the backend. The result is `nil` or has a readable `Err` (`resultErrOk`), the id is
  `rq`'s.
* **The KV** (unit 2): the apply thread's applier state `applyKV E ua x` (the uber-applier's
  current chain, the KV's committed log), with the request's premises at `x.log` (`rqOk`: the txn
  package's for a KV request; `dispatchOk`: not a compaction, not empty), goes to `x'` by
  `applyStep rq v3 x x' out`: skipped or rejected by the admin check (`x' = x`), or dispatched
  (`dispatchStep`: a KV request as the chain's `chainStep backendStep`, the txn package's results;
  without `v3`, nothing), the result `applyResultIs`. -/
abbrev apply.Apply.spec : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : AEnv GF)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : IRRModel) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.applierFor ua E ∗ waitOk w ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
      (if v3 then iprop(□ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
          (Q ={⊤}=∗ E.P ∗ Post))
       else iprop(True)) ∗ Pre ∗
      apply.applyKV E ua x ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.rqOk x.log rq ∧
        apply.dispatchOk rq⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id' : w64), RET (PairV #ar #id');
      (if v3 then iprop(Post ∨ Pre) else Pre) ∗ apply.resultErrOk ar ∗ ⌜id' = id⌝ ∗
      ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), apply.applyKV E ua x' ∗
        ⌜apply.applyStep rq v3 x x' out⌝ ∗ apply.applyResultIs rq v3 x.log ar out }}

end spec

end EtcdGrove
end Perennial
