/-
`apply.Apply(lg, e, uberApply, w, shouldApplyV3)` (`apply.go:27-49`): decode the entry's
`InternalRaftRequest` (`pbutil.MustUnmarshalMessage`: panics on bytes that do not decode), take its
id (`ID`, or the header's; `lg.Panic` with neither), ask the wait registry whether anyone waits
(`w.IsRegistered(id)`), and either call the uber-applier's `Apply` on a wrapper (`SkipRangeExecution`
for a transaction no one waits for) or, for an unregistered request without side effects (a range,
a user or role read, the auth status), return `nil`.

**Users.** `EtcdServer.applyEntryNormal` (`server.go:1994`, 2d's `applyEntryNormal.spec`: `ua` the
server's `s.uberApply`, `w` its `s.w`, a `*wait.list`). Snippets `examples/specreq/apply/apply.go`
(`ReqApplyWrite`, `ReqApplyReplay`, `ReqApplyNoResult`).

**Proof sketch.** `MustUnmarshalMessage` (4b's `pbutil`, provisional: a fresh message with
`irrMsgAt p ir` given `irrDecodes e.Data ir`; 2d's `entryAt` gives `e.Data`). `lg.Debug` (`Zap`,
`zap.Stringer` lazy). The id: `ir.reqId` (`hasId` rules out the panic). `w.IsRegistered(id)` through
the interface (`w` is a `*list`: 2c's `Wait.list.IsRegistered.spec`, with the waiter fact and the
thread token; `false` gives `waitDone`). The wrapper allocated (`wrapperAt r ir sk`, `sk = !registered && Txn != nil`). Then the
caller's method triple (`P` to `Q sk ar`), or `nil` with `P` untouched.

**Changes** from `specs-ref`'s `Apply.lean` (the approved shape of
`.claude/skills/spec/examples/apply-uber-contract.md`): the request is `Irr` (W0-level), not the old
`IRRModel`; the wait registry is 2c's `listAt` with its waiter facts (`waitWasReg`/`waitNever` in,
`waitDone` out), not `waitOk`'s `RD`/`K`/`G`.

**Margin.** None. (Round 1: the waiter's fact `waitWasReg ∨ waitNever` taken, as 2c's
`list.IsRegistered.spec` needs; its `false` answer's `waitDone` given back for a skipped transaction and
on the `nil` path, as the approved example's `G ot id`: 2d's `applyEntryNormal` then owes the waiter
nothing.)
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiApply
public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.wait.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **Apply a committed entry through the uber-applier's method**, whose contract (`P` to `Q`) the
caller gives (`isUber_apply`): the method's result for the decoded request, or `nil` without a call
for an unregistered request without side effects. The id returned is the request's. -/
def Apply.spec : Prop :=
  ∀ (lg ptr : Loc) (k : Nat) (ent : Raft.LogEntry) (ir : Irr) (ua w : GoInterface) (l : Loc)
    (γw : Wait.WaitNames) (Pw : w64 → GoInterface → IProp GF) (v3 : Bool)
    (P : IProp GF) (Q : Bool → Loc → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      Zap.isLogger lg ∗ EtcdServer.entryAt ptr k ent ∗ ⌜irrDecodes ent.data ir ∧ ir.hasId⌝ ∗
      ⌜w = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.list'.ty) #l⌝ ∗
      Wait.listAt l γw Pw ∗ (Wait.waitWasReg γw ir.reqId ∨ Wait.waitNever γw ir.reqId) ∗ threadTok ∗
      (∃ ui : GoInterfaceOk, ⌜ua = GoInterface.ok ui⌝ ∗
        □ ∀ (r : Loc) (sk : Bool),
          {{ wrapperAt r ir sk ∗ ⌜sk = true → ir.op.isTxn = true⌝ ∗ threadTok ∗ P }}
            (App (App (Val #(methods ui.ty go!"Apply" ui.v)) (Val #r)) (Val #v3))
          {{ (ar : Loc), RET #ar; threadTok ∗ Q sk ar }}) ∗ P }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #ptr)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id : w64), RET (PairV #ar #id); threadTok ∗ ⌜id = ir.reqId⌝ ∗
      ((∃ sk : Bool, Q sk ar ∗ (⌜sk = false⌝ ∨ Wait.waitDone γw ir.reqId)) ∨
       (⌜ar = null ∧ ir.op.noSideEffect = true⌝ ∗ Wait.waitDone γw ir.reqId ∗ P)) }}

end spec

end Apply
end EtcdGrove
end Perennial
