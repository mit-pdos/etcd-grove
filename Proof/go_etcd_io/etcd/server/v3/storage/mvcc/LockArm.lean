/-
**A critical section of the batch lock by the post-lock hook's state** (M2, the storage side, item
31, 2026-10-30): `SetScheduledCompact`'s `LockInsideApply` runs the hook if one is set
(`batch_tx.go:111-122`). The hook is set on every backend the server applies to, but not yet on the
new backend `kv.Restore` installs while `restore()` resumes a scheduled compaction (the server sets
it after `Restore` returns, `server.go:1089-1093`): there the lock runs nothing.

- `lockNilSpec` (moved from `M2StorageDraftRestore.lean`): `LockInsideApply` with no hook set, from
  the session's tokens and the unset hook `HN`, gives the lock, its resource `W` and the batch lock's
  invariant `P` itself. The real backend gives it (`bt_lockInNil`, from the backend spec's nil arm).
- `lockArmS`: what a caller of `SetScheduledCompact` brings for the critical section, by the hook's
  state: set to `f` (the hook's `HF f`, its triple and the caller's update with the hook's `Q`), or
  unset (`HN`, `lockNilSpec` and the caller's update from `Pre`, `P` passing through).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section arm
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`LockInsideApply` with no hook set**: from the session's tokens and the unset hook `HN`, the
lock, its resource `W` and the batch lock's invariant `P` itself (no hook ran). -/
def lockNilSpec (bt : GoInterfaceOk) (RT WT W P HN : IProp GF) (Locked : Puts → IProp GF) :
    IProp GF :=
  iprop(□ (∀ Pre : IProp GF,
    {{ Pre ∗ RT ∗ WT ∗ HN }} (App (Val #(methods bt.ty go!"LockInsideApply" bt.v)) (Val #()))
    {{ RET #(); Locked [] ∗ W ∗ P ∗ Pre ∗ RT ∗ HN }}))

instance lockNilSpec_persistent (bt : GoInterfaceOk) (RT WT W P HN : IProp GF)
    (Locked : Puts → IProp GF) : Persistent (lockNilSpec bt RT WT W P HN Locked) := by
  unfold lockNilSpec; infer_instance

/-- **The critical section's context, by the hook's state** (`SetScheduledCompact`'s): set to `f`,
the hook's `HF f`, its triple `{P ∗ Pre} f() {Q}` and the caller's update `Q ∗ W ={⊤}=∗ P ∗ W ∗
Post`; unset, the unset hook `HN` with `LockInsideApply`'s nil arm (`lockNilSpec`), and the caller's
update `Pre ∗ HN ={⊤}=∗ Post` (the hook given back through it). -/
def lockArmS (bt : GoInterfaceOk) (RT WT W P : IProp GF) (HF : val → IProp GF)
    (Locked : Puts → IProp GF) (HN : IProp GF) (hk : Option val) (Pre Q Post : IProp GF) :
    IProp GF :=
  match hk with
  | some f => iprop(HF f ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
      (Q ∗ W ={⊤}=∗ P ∗ W ∗ Post))
  | none => iprop(HN ∗ lockNilSpec bt RT WT W P HN Locked ∗ (Pre ∗ HN ={⊤}=∗ Post))

theorem lockArmS_some (bt : GoInterfaceOk) (RT WT W P : IProp GF) (HF : val → IProp GF)
    (Locked : Puts → IProp GF) (HN : IProp GF) (f : val) (Pre Q Post : IProp GF) :
    lockArmS bt RT WT W P HF Locked HN (some f) Pre Q Post =
      iprop(HF f ∗ □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗
        (Q ∗ W ={⊤}=∗ P ∗ W ∗ Post)) := rfl

theorem lockArmS_none (bt : GoInterfaceOk) (RT WT W P : IProp GF) (HF : val → IProp GF)
    (Locked : Puts → IProp GF) (HN : IProp GF) (Pre Q Post : IProp GF) :
    lockArmS bt RT WT W P HF Locked HN none Pre Q Post =
      iprop(HN ∗ lockNilSpec bt RT WT W P HN Locked ∗ (Pre ∗ HN ={⊤}=∗ Post)) := rfl

end arm

end mvcc
end EtcdGrove
end Perennial
