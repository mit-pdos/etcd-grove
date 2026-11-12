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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`apply.Apply(lg, e, uberApply, w, shouldApplyV3)`, over the uber-applier's contract** (step 6
of the auth-mode merge, 2026-10-30; `notes/decisions.md`, "Step 6: one `apply.Apply.spec`"). It
decodes the entry `e`'s request `rq` (the premise: its data decode, `irrDecode`), computes its id
(`irrId rq = some id`: an id, or a header's), asks the waiter (`w.IsRegistered(id)`, with the
reader's resource `RD` of the wait, `waitOk`, given back) and then either calls the
`UberApplier` interface's `Apply` method on a wrapper of `rq` (`irrWrapperIs`) whose skip flag `sk`
is `!registered && rq.Txn != nil` (so `sk` implies a transaction), or, for an unregistered request
with no side effects (`noSideEffect`), returns `nil` without calling it.
The method's contract is the caller's: a triple from `P` to `Q sk ar` at every wrapper of `rq`
(the uber-applier's own specs give it: `uberApplier.Apply.spec`, `kvSpecL`, `adminSpecL`; the
corollaries in `ApplyRec.lean`). The result is the method's `ar` with `Q sk ar`, and, for a
skipping wrapper (`sk = true`), what `IsRegistered`'s `false` told the caller about the id
(`G ot id`); or `nil` with `G ot id` and `P` back. The id is `rq`'s. -/
abbrev apply.Apply.spec : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (rq : IRRModel) (id : w64)
    (RD : IProp GF) (K G : Option GName → w64 → IProp GF) (ot : Option GName)
    (P : IProp GF) (Q : Bool → Loc → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ ∗
      (∃ ui : GoInterfaceOk, ⌜ua = GoInterface.ok ui⌝ ∗
        □ ∀ (r : Loc) (sk : Bool),
          {{ apply.irrWrapperIs r rq sk ∗ ⌜sk = true → rq.txn.isSome = true⌝ ∗ P }}
            (App (App (Val #(methods ui.ty go!"Apply" ui.v)) (Val #r)) (Val #v3))
          {{ (ar : Loc), RET #ar; Q sk ar }}) ∗ P }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗ ⌜id' = id⌝ ∗
      ((∃ sk : Bool, Q sk ar ∗ (⌜sk = false⌝ ∨ G ot id)) ∨
       (⌜ar = null ∧ apply.noSideEffect rq = true⌝ ∗ G ot id ∗ P)) }}

end spec

end EtcdGrove
end Perennial
