/-
`store.applyEventsLocked(events)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `s.applyEventsLocked(events)`, under the write lock: the physical state becomes
`(applyEvents cap st evs).1`, and the error is `nil` iff `(applyEvents cap st evs).2`. The
events must be in revision order and above the latest revision (what `Apply`'s
`validateRevisions` checks), so that the history's revisions increase, and certified
(`snapCerts E (applyEventsSnaps st.latest evs)`: every snapshot it appends). -/
abbrev store.applyEventsLocked.spec : Prop :=
  ∀ (s : Loc) (γ : StoreNames) (cap : Nat) (E : w64 → KvMap → IProp GF) (st : StoreState) (evSl : GoSlice)
    (evs : List EvModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isStore s γ cap ∗ storeLockedPhys s cap E st ∗ ⌜StoreInv cap st⌝ ∗ eventsAt evSl evs ∗
      ⌜EvRevSorted evs ∧ ∀ e ∈ evs, sint.Z st.latestRev < sint.Z e.rev⌝ ∗
      snapCerts E (applyEventsSnaps st.latest evs) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"applyEventsLocked")) (Val #evSl))
  {{ (err : GoInterface), RET #err;
      storeLockedPhys s cap E (applyEvents cap st evs).1 ∗
      ⌜StoreInv cap (applyEvents cap st evs).1 ∧
        sint.Z st.latestRev ≤ sint.Z (applyEvents cap st evs).1.latestRev⌝ ∗
      ⌜if (applyEvents cap st evs).2 then err = GoInterface.nil
        else ∃ e, err = GoInterface.ok e⌝ }}

end spec

end EtcdGrove
end Perennial
