/-
**mvcc's store over the real backend** (unit 5): `store.Write` stated over the
backend's proved contract (`isBackend`, through the bridge `storeBackend_of_backend`) instead of
mvcc's assumed one. Lean-first; `notes/decisions.md`, "The store over the real backend (unit 5)".

The store is of the real instance `d` (`StoreNames.kb = some d`): its view of the `Key` bucket is
the backend's clients' view (`bkView d.γB`), its reader slots carry a reader's slot of the
backend and a share of it open (`bkRTx`), its writes spend a write-back's budget (`wbTok`), its
puts meet the safe-range condition (`keyPutOk`: proved of mvcc's revision keys,
`storePutOk_next`), and the backend's batch lock holds the store's writer's resource through the
late-bound `lateW d.gx`, registered by `NewStore`'s first `Unlock`. The other mvcc results are
generic in the instance: at `γ.kb = some d` they are over the real backend. The compaction's
(units 5a-5c) are not: they need a backend that supports it (`storeCmp`, false of the real
instance: its model forbids deleting from the safe-range `Key` bucket; `notes/decisions.md`, "The
compaction over the real backend"), so a store of the real instance is used frozen
(`compactRight_freeze`, `storeReaders_of`).

(mvccfull's Freeze, 2026-11-10) `NewStore_backend`, `NewStore` over the real backend, a corollary of
the fresh internal `NewStore.spec` that no linked result used, is removed: the restated spec takes
the lessor's owner part, which it did not have (its text at commit `ae30739dde`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ReaderSpecs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **`store.Write` over the real backend**: the generic `store.Write` at a store of the real
instance `d`, its write token the backend's write-back budget. -/
theorem mvcc.store_Write_backend (hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : mvcc.StoreNames) (d : mvcc.KBReal) (hk : γ.kb = some d) (trace : Loc)
    (P Pre Q : IProp GF) (f : val) (te : Bool) (G : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        mvcc.isStore s γ ∗ mvcc.storeReader s γ ∗ backend.wbTok d.γB ∗
        ⌜trace ≠ null⌝ ∗ mvcc.hookIs γ P f ∗ Pre ∗
        □ ({{ P ∗ Pre }} (App (Val f) (Val #())) {{ RET #(); Q }}) ∗ traceutil.ownTrace trace te ∗
        G ∗ □ (mvcc.slotF γ ∗ G -∗ False) }}
      (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Write")) (Val #trace))
    {{ (mw : Loc), RET #(interface.mkOk (go.GoType.PointerType metricsTxnWrite.ty) #mw);
        (∃ (ilog : mvcc.Log) (crev : Int),
          mvcc.isTxnWrite mw s γ trace ilog [] (W64 0) (W64 0) (W64 0) crev) ∗
        Q ∗ G }} := by
  have hWrite := mvcc.store.Write.spec_R hWrite
  have hwt : mvcc.storeWT (GF := GF) γ = backend.wbTok d.γB := by
    unfold mvcc.storeWT mvcc.kbWT; rw [hk]
  rw [← hwt]
  iintro %Φ H HΦ
  iapply (hWrite s γ trace P Pre Q f te G) $$ %Φ [H]
  · iexact H
  inext
  iintro %mw ⟨⟨%ilog, %crev, Htx, -⟩, HQ, -, HG⟩
  iapply HΦ
  iframe HQ HG
  iexists ilog, crev
  iexact Htx

end proof

end EtcdGrove
end Perennial
