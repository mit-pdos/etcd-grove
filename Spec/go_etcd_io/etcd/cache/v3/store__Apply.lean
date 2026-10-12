/-
`store.Apply(resp)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `s.Apply(resp)`, by any writer (`isStoreWriter`): under the write lock, with the store in some
state `st` (found there: any number of writers apply in turn), the state becomes
`(applyResp cap st r).1`, and the error is `nil` iff `(applyResp cap st r).2` (see `applyResp`
for the cases: a canceled response, or one `validateRevisions` rejects as stale, changes
nothing). The events must be in revision order (`EvRevSorted`, as etcd sends them). The caller
holds a lower bound `lo` on the newest snapshot (`storeSnapLb`) and certifies what `Apply` would
do to any state at or above it (`storeApplyCert`: it changes nothing or succeeds, with every
snapshot it appends and every revision it moves to certified), so that the store stays
certified and synced whoever writes. The state found had a newest snapshot, the latest map, at a
revision at least `lo`; afterwards the latest revision and the newest snapshot are at least
those of `(applyResp cap st r).1`. (A canceled response is rejected before the lock: just an
error.) An error's `Error()` returns some string (`errStrOk`: `errors.New`'s or `fmt.Errorf`'s). -/
abbrev store.Apply.spec : Prop :=
  ∀ (s : Loc) (γ : StoreNames) (cap : Nat) (E : w64 → KvMap → IProp GF) (R : w64 → IProp GF)
    (lo : w64) (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isStore s γ cap ∗ isStoreWriter s γ cap E R ∗ respAt resp r ∗ ⌜EvRevSorted r.events⌝ ∗
      storeSnapLb γ lo ∗ ⌜0 ≤ sint.Z lo⌝ ∗ storeApplyCert cap E R lo r }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Apply")) (Val #resp))
  {{ (err : GoInterface), RET #err; errStrOk err ∗ (⌜r.canceled = true ∧ ∃ e, err = GoInterface.ok e⌝ ∨
      ∃ st : StoreState,
      ⌜StoreInv cap st ∧ st.Synced ∧
        ∃ Y : w64, st.history.getLast? = some (Y, st.latest) ∧ sint.Z lo ≤ sint.Z Y⌝ ∗
      storeRevLb γ (applyResp cap st r).1.latestRev ∗
      monoNatLbOwn γ.snap (storeSnapKey (applyResp cap st r).1) ∗
      ⌜if (applyResp cap st r).2 then err = GoInterface.nil else ∃ e, err = GoInterface.ok e⌝) }}

end spec

end EtcdGrove
end Perennial
