/-
**`applySnapshot`'s open of the snapshot's backend** (D22 receiver epochs, S8d, 2026-10-26;
`notes/snapshot-s8-plan.md`): lemmas outside the spec/proof discipline (ghost steps, no code).

* `snap_create`: `OpenSnapshotBackend`'s creation step (`openPre`'s wand) for the backend the apply
  thread opens: the store's late registration slot, the batch lock's resource at the announced
  physical names (`ci_announce`) and what `applySnapshot` keeps (`snapOpenK`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **What `applySnapshot` keeps of a backend it opens** (D22 receiver epochs, S8d): the
announcement of the fresh physical names `futPhys π0 γB` in the protocol's futures (its claim
token and index), which `ci_swap_au` turns into the registration at `SetBackend`, and the new
backend's close right (`γB.cls`, which the futures' deposit does not name). -/
def snapOpenK (γA : ApplyNames) (π0 : ApplyPhys) (γB : backend.BNames) : IProp GF :=
  iprop(ghostVar γB.cls 1 () ∗
    ∃ (j : Nat) (γc : GName), token γc ∗ monoListIdxOwn γA.fut j (futPhys π0 γB, γc))

/-- **The creation step of the backend `applySnapshot` opens** (`openPre`'s wand): the fresh
backend's own keys (at the image `D`, whose meta keys are `π0.m0`) and payment rights give the
store's late registration slot `lateW gx`, the batch lock's resource at the announced names
(`ci_announce`: the payment rights deposited in the futures) and the announcement. -/
theorem snap_create (γA : ApplyNames) (π0 : ApplyPhys) (P : backend.BParams) (D : backend.Data)
    (gx : GName) (hm : metaIs D π0.m0) :
    inv applyN (consInv (GF := GF) γA) ⊢ token π0.pend -∗ ghostVar π0.mt (1 : Qp).half π0.m0.1 -∗
      mvcc.lateW gx -∗
      ∀ γB : backend.BNames, backend.hkOwn γB (backend.hkData P D) ∗ backend.bFresh γB ={⊤}=∗
        mvcc.lateW gx ∗ batchLockInv (γA.withPh (futPhys π0 γB)) (metaTM γB P) ∗
        snapOpenK γA π0 γB := by
  iintro #Hinv Hpend Hmt HW %γB ⟨Hk, Hfr⟩
  ihave HTM : metaTM (GF := GF) γB P π0.m0 $$ [Hk]
  · iunfold metaTM; iexists D; iframe Hk; ipureintro; exact hm
  imod ci_announce γA (futPhys π0 γB) γB (metaTM γB P) π0.m0 rfl rfl $$ Hinv Hfr Hpend Hmt HTM
    with ⟨Hbl, Hcls, %j, %γc, Htc, #Hidx⟩
  imodintro
  iframe HW Hbl
  iunfold snapOpenK
  iframe Hcls
  iexists j, γc
  iframe Htc Hidx

section swap
variable [cindex_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- **`ci.SetBackend(newbe)` by the apply thread** (`ci_swap_au` at `SetBackend`'s linearization
point): the protocol moves to the announced names `π'` at the state `s'`; the apply thread gets its
state there, their registration, the new backend's deposited payment rights (`futStash`) and the
consistent index's owner share at `newbe`. -/
theorem wp_ci_swap (hSB : consistentIndex.SetBackend.spec (GF := GF) (hG := hG))
    (γ : ApplyNames) (ci : Loc) (s s' : ApplyState) (π' : ApplyPhys) (j : Nat) (γc : GName)
    (b be : GoInterface)
    (hk' : s'.k = W64 0) (hps' : s'.pending = false) (hok : stOk (γ.withPh π') s')
    (hle : uint.Z (ciEff γ s.k) ≤ uint.Z π'.m0.1) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
        isCI ci γ.ci ∗ inv applyN (consInv γ) ∗ applyThread γ s ∗ ciOwner ci b ∗
        ghostVar π'.mt (1 : Qp).half π'.m0.1 ∗ ghostVar π'.wr 1 false ∗ token γc ∗
        monoListIdxOwn γ.fut j (π', γc)) -∗
      (applyThread (γ.withPh π') s' ∗ applyRegd (γ.withPh π') ∗ futStash π' ∗ ciOwner ci be -∗
        Φ #()) -∗
      WP (App (Val (ci @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty @!! go!"SetBackend"))
        (Val #be)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hci, #Hinv, Hst, Hown, Hmt, Hwr, Htc, #Hidx⟩ HΦ
  iapply (hSB ci γ.ci b be) $$ [Hown] [HΦ Hst Hmt Hwr Htc]
  · iframe Hpkg Hci Hown
  iapply ci_swap_au γ s s' π' j γc (iprop(ciOwner ci be -∗ Φ #())) hk' hps' hok hle
    $$ Hinv Hst Hmt Hwr Htc Hidx
  iintro Hst Hreg Hfs Hown
  iapply HΦ
  iframe

end swap

end lemmas

end EtcdGrove
end Perennial
