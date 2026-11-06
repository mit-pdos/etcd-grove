/-
**The server's store invariant's laws** (strict M1, 2026-11-05): the draft's `kvAus.law`,
`kvPeek.law`, `crevOk_off.law`, `histLb_boot.law` and `bootStore.law` (`KVStoreApi.lean`), each the
generic one of `KVStoreCore.lean` at the raft witness `kvNx γr on` and the compaction permit
`crevOk γr` (`kvStoreInv_eq`, by `rfl`), over mvcc's API laws as hypotheses (`persistent.law`,
`mvccState_reachable.law`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStoreApi

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section
namespace Perennial
namespace EtcdGrove
namespace srvApi
open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc mvcc.api

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- `apply.cmpRevAfter` is the core's `crevAfter`. -/
theorem cmpRevAfter_eq (c : Int) (rev : w64) : apply.cmpRevAfter c rev = crevAfter c rev := rfl

/-- **The builders** (`kvAus.law`). -/
theorem kvAus_holds (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF)) :
    kvAus.law (GF := GF) := by
  intro kv γ γr on γs
  rw [kvStoreInv_eq]
  simp only [cmpRevAfter_eq, kvReadAt_eq]
  exact kvAusG (kvNx γr on) (crevOk γr) Hp Hr kv γ γs

/-- **The watch path's peek** (`kvPeek.law`). -/
theorem kvPeek_holds (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF)) :
    kvPeek.law (GF := GF) := by
  intro kv γ γr on γs E hE
  rw [kvStoreInv_eq]
  simp only [histLb_eq]
  exact kvPeekG (kvNx γr on) (crevOk γr) Hp Hr kv γ γs E hE

/-- **The never-compacting cluster's compaction revision** (`crevOk_off.law`). -/
theorem crevOk_off_holds : crevOk_off.law (GF := GF) := by
  intro γr c h
  iintro H
  iunfold crevOk at H
  icases H with ⟨-, %H⟩
  ipureintro; exact H h

/-- **The boot's bound** (`histLb_boot.law`). -/
theorem histLb_boot_holds (Hp : persistent.law (GF := GF))
    (Hr : mvccState_reachable.law (GF := GF)) : histLb_boot.law (GF := GF) := by
  intro kv γ γr on γs
  rw [kvStoreInv_eq, histLb_eq]
  exact histLb_bootG (kvNx γr on) (crevOk γr) Hp Hr kv γ γs

/-- **The boot's store invariant** (`bootStore.law`): the witness of the empty history from the
committed raft log's empty prefix, the permit of `-1`. -/
theorem bootStore_holds (Hp : persistent.law (GF := GF)) : bootStore.law (GF := GF) := by
  intro kv γ γr on γs h0
  haveI := Hp.1 kv γ
  rw [kvStoreInv_eq]
  iintro ⟨#Hm, Hs, Hf, #Hlb⟩
  iunfold newServerStoreFreshA at Hf
  icases Hf with ⟨Hst, Hcr, Hsl, Hnl⟩
  iapply bootStoreG (kvNx γr on) (crevOk γr) Hp kv γ γs
  iframe Hm Hs Hst Hcr Hsl Hnl
  isplitl []
  · iunfold kvNx
    iexists []
    iframe Hlb
    ipureintro; exact h0
  iunfold crevOk
  isplitl []
  · ileft; ipureintro; rfl
  ipureintro; intro _; rfl

/-- The mode-off raft witness is `KVApply`'s `kvNxOff` (by `rfl`). -/
theorem kvNx_off (γr : ReadNames) : kvNx (GF := GF) γr false = kvNxOff γr.raft γr.kv := rfl

/-- **The server's witness and permit are persistent and timeless** (`envWitOk`, which the
apply thread's `srvKVInvs` carries). -/
theorem envWitOk_srv (E : apply.AEnv GF) (γr : ReadNames) (on : Bool)
    (hNx : E.Nx = kvNx γr on) (hCp : E.Cp = crevOk γr) : envWitOk E := by
  unfold envWitOk; rw [hNx, hCp]
  exact ⟨fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance⟩

/-- **The draft's `srvKVInvsA` from the apply thread's `srvKVInvs`** and the ties of the store
handle, the witness and the permit (strict M1, 2026-11-05: `srvKVInvs`, below the KV model, has
no tie naming it; the server's mode-level facts carry them). -/
theorem srvKVInvsA_of (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (wsl : Loc)
    (h : E.kv = wsIfaceA wsl ∧ E.Nx = kvNx γr on ∧ E.Cp = crevOk γr) :
    srvKVInvs (GF := GF) E γr ⊢ srvKVInvsA on E γr wsl := by
  iintro H
  iunfold srvKVInvs at H
  icases H with ⟨#Hk, -, #Hr, #Hs, %Hm, -⟩
  iunfold srvKVInvsA
  iframe Hk Hr
  isplitl
  · rw [kvStoreInv_eq, ← h.2.1, ← h.2.2]; iexact Hs
  · ipureintro; exact ⟨h.1, h.2.1, h.2.2, Hm.1, Hm.2.1⟩

/-- **The apply thread's `srvKVInvs` from the store invariant**, the KV and raft invariants and the
KV certificates' (`kvCertInv`, the server's own), at the server's witness and permit (the mode
off: `srvKVInvs` ties `E.Nx` to `kvNxOff`, 2026-11-06). -/
theorem srvKVInvs_of (Hp : persistent.law (GF := GF)) (E : apply.AEnv GF)
    (γr : ReadNames) (hNx : E.Nx = kvNx γr false) (hCp : E.Cp = crevOk γr)
    (hm : γr.kv.cmp = E.cmp ∧ γr.kv.cret = E.cret) :
    kvInv (GF := GF) γr.raft γr.kv ∗ kvCertInv γr.raft γr.kv ∗ srvRaftLogInv γr.raft ∗
      kvStoreInv E.kv E.γ γr false E.γs ⊢ srvKVInvs E γr := by
  haveI : Persistent (kvStoreInv (GF := GF) E.kv E.γ γr false E.γs) := by
    rw [kvStoreInv_eq]; exact kvStoreInvG_persistent Hp E.kv E.γ (kvNx γr false) (crevOk γr) E.γs
  iintro ⟨#Hk, #Hc, #Hr, #Hs⟩
  iunfold srvKVInvs
  iframe Hk Hc Hr
  isplitl
  · rw [hNx, hCp, ← kvStoreInv_eq]; iexact Hs
  isplitl
  · ipureintro; exact ⟨hm.1, hm.2, envWitOk_srv E γr false hNx hCp, hCp⟩
  · ipureintro; exact hNx

end laws

/-! ## The sender's image (§3b-§3c) -/

section snap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [bk_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **The snapshot at the writer's state, generic** (§3b's composition): `mvccImage_snapshot.law`
at the update `kvAus`' snapshot builder makes from the store invariant (`au_snap`) and the writer's
half `wSt γs log c` (given back): the snapshot's data `D` is the image of `(log, c)`, the client's
observation `Q` holds. What `senderImage.law` (the mode off, at the model's state) and the merged
snapshot's window (`SnapSendBranch.mergedCreate_window`, either auth mode) use. -/
theorem snapImageG (Hp : persistent.law (GF := GF)) (Hr : mvccState_reachable.law (GF := GF))
    (hImg : mvccImage_snapshot.law (GF := GF) (hG := hG))
    (hSnap : backend.backend.Snapshot.spec (GF := GF) (hG := hG))
    (Nx : mvcc.Log → IProp GF) (Cp : Int → IProp GF)
    [∀ l, Persistent (Nx l)] [∀ l, Timeless (Nx l)] [∀ c, Persistent (Cp c)]
    [∀ c, Timeless (Cp c)] (kv : GoInterface) (γ : MvccName)
    (γs : KVSNames) (log : mvcc.Log) (c : Int) (bk : mvcc.KBReal) (Pk : IProp GF) (qo : Qp)
    (R : IProp GF)
    (Q : GMap (GoString × GoString) GoString → GMap GoString backend.BktData → Prop) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      kvStoreInvG kv γ Nx Cp γs ∗ wSt γs log c ∗ mvccBackend γ 1 (etcdStorage bk) Pk ∗
      backend.bOpen bk.γB qo ∗ backend.wbTok bk.γB ∗ R ∗
      □ (∀ (d : GMap (GoString × GoString) GoString) (r : GMap GoString backend.BktData),
        R -∗ Pk -∗ backend.hkOwn bk.γB d -∗ backend.rbOwn bk.γB r -∗ ⌜Q d r⌝) }}
    (App (Val (bk.be @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty
      @!! go!"Snapshot")) (Val #()))
  {{ (sp : Loc) (D : backend.Data),
      RET #(interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #sp);
      backend.snapOpen sp D ∗ backend.bOpen bk.γB qo ∗ R ∗ mvccBackend γ 1 (etcdStorage bk) Pk ∗
      wSt γs log c ∗ ⌜Q (backend.hkData bk.P D) (backend.rbData bk.P D)⌝ ∗
      ⌜imageStOk log c⌝ ∗ ∃ u : Bool, mvccImage D log c u }} := by
  haveI := kvStoreInvG_persistent Hp kv γ Nx Cp γs
  iintro %Ψ ⟨#Hpkg, #Hk, Hw, HB, Ho, Hwb, HR, #HQ⟩ HΨ
  -- the writer's state reachable (the image certificate carries it to the receiver's `Restore`)
  imod writer_facts Nx Cp Hp Hr kv γ γs log c $$ Hk Hw with ⟨Hw, -, -, -, %Hre⟩
  ihave HAU := au_snap Nx Cp Hp kv γ γs log c (wSt γs log c) $$ Hk Hw []
  · iintro H; iexact H
  ihave #Hk' := Hk
  iunfold kvStoreInvG at Hk'
  icases Hk' with ⟨#Hm, -⟩
  iunfold auSnap at HAU
  iapply (hImg hSnap kv γ bk Pk qo R Q (fun σ => iprop(⌜σ = stAt log c⌝ ∗ wSt γs log c)))
    $$ [HB Ho Hwb HR HAU]
  · iframe #; iframe
  iintro !> %sp %D ⟨Hsn, Ho, HR, HB, %HQD, %σ, %u, ⟨%Hσ, Hw⟩, #Him⟩
  subst Hσ
  iapply HΨ
  iframe
  isplitr
  · ipureintro; exact HQD
  isplitr
  · ipureintro; exact Hre
  iexists u
  rw [show (stAt log c).log = log from rfl, show (stAt log c).crev = c from rfl]
  iexact Him

/-- **The merged snapshot's send** (`senderImage.law`, proved): `snapImageG` at the model's state
`(kvModel A, crevOf A)`, the image certificate `dbImageA` from the client's observation
(`dbImageA_of_send`). -/
theorem senderImage_holds (Hp : persistent.law (GF := GF))
    (Hr : mvccState_reachable.law (GF := GF)) : senderImage.law (GF := GF) := by
  intro hSnap hImg _ kv γ γr γs i A B Pk qo R Q hQ hi
  rw [kvStoreInv_eq]
  haveI := kvStoreInvG_persistent Hp kv γ (kvNx γr false) (crevOk γr) γs
  iintro %Ψ ⟨#Hpkg, #Hk, Hw, #Hlb, HB, Ho, Hwb, HR, #HQ⟩ HΨ
  iapply (snapImageG Hp Hr hImg hSnap (kvNx γr false) (crevOk γr) kv γ γs (kvModel γr.kv A)
    (crevOf γr.kv A) B Pk qo R Q) $$ [Hw HB Ho Hwb HR]
  · iframe #; iframe
  iintro !> %sp %D ⟨Hsn, Ho, HR, HB, Hw, %HQD, %Hre, %u, #Him⟩
  iapply HΨ
  iframe
  iapply (dbImageA_of_send γr.raft γr.kv i D A u hi (hQ D HQD) Hre)
  iframe Hlb Him

/-! ## The Restore builder (§3d) -/

/-- **The KV model is monotone in the raft log, in either mode** (off: `kvRaftOf_prefix`; on:
`kvRaftOfOn_prefix`, `KVAuthModel`). -/
theorem kvModelM_prefix (on : Bool) (γk : KVNames) (A A' : List EntryModel) (h : A <+: A') :
    kvModelM on γk A <+: kvModelM on γk A' := by
  cases on
  · exact kvRaftOf_prefix _ _ _ _ _ h
  · exact kvRaftOfOn_prefix _ _ _ _ _ h

/-- **The Restore builder, proved** (`restoreArgs.law`): `au_restore` at the raft witness
`kvNx γr on` of the snapshot's log `A'` and the permit `crevOk γr` of its compaction revision, the
restored state extending the apply thread's (`kvModelM_prefix`, `crevOf_mono`); the store's handle
from the store invariant, the commit request `True ⇒ True` (`backend.commitReq_true`). -/
theorem restoreArgs_holds (Hp : persistent.law (GF := GF)) : restoreArgs.law (GF := GF) := by
  intro kv γ γr on γs log c A A' B B' Pk Pk' u Ls dq f Pre Q' Post
  dsimp only
  intro hlog hc hAA hre hit
  rw [kvStoreInv_eq]
  haveI := kvStoreInvG_persistent Hp kv γ (kvNx γr on) (crevOk γr) γs
  simp only [stAt_log, stAt_crev] at hit ⊢
  iintro ⟨#Hk, Hw, Hc, #Hlb, #Hcp, Ht, Ho, HB, HB', Hh, HPre, Hrun, HQ', Hl⟩
  have hl : log <+: kvModelM on γr.kv A' := by
    rw [hlog]; exact kvModelM_prefix on γr.kv A A' hAA
  have hcc : c ≤ crevOf γr.kv A' := by
    rw [hc]; exact crevOf_mono γr.kv A A' hAA
  ihave #Hnx : kvNx (GF := GF) γr on (kvModelM on γr.kv A') $$ []
  · iunfold kvNx; iexists A'; iframe Hlb; ipureintro; rfl
  ihave HAU := au_restore (kvNx γr on) (crevOk γr) Hp kv γ γs log (kvModelM on γr.kv A') c
    (crevOf γr.kv A') hl hcc $$ Hk Hw Hc Hnx Hcp
  ihave #Hk' := Hk
  iunfold kvStoreInvG at Hk'
  icases Hk' with ⟨#Hm, -⟩
  iunfold restorePreA
  simp only [stAt_log, stAt_crev, stAt_pending]
  iframe Hm Ht Ho HB HB' Hh HPre Hrun HQ' Hl HAU
  isplitr
  · ipureintro; exact ⟨hre, trivial⟩
  isplitr
  · iapply (backend.commitReq_true (GF := GF) B'.γB B'.P Pk' B'.be)
  ipureintro; exact hit

end snap

end srvApi
end EtcdGrove
end Perennial
