/-
**`NewStorage`'s contract proved** (wal-link L3, 2026-11-19; `notes/wal-link-l3-statements.md` §2, §4): the
storage `serverstorage.NewStorage(lg, h.w, ss)` returns meets the WAL contract (`isWalStorage st h ss`), each
law from the storage method's spec over the real WAL (`Spec/.../storage/storage__*.lean`, at the server's
message model `walSrvP`/`walSrvMr` and the open WAL `h`'s file-system instances), the records' atomic
updates turned into layer 1's (`walRecs` is the fold of layer 1's history, `storage/WalRecs.lean`). Until
L3 `rnNewStorageOk` was a premise of every closed theorem. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.WalApi
public import Spec.go_etcd_io.etcd.server.v3.storage.NewStorage
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Save
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__SaveSnap
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Sync
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.storage__Release

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The storage methods' specs at the open WAL `h`'s instances** (the server's message model): what
`rnNewStorageOk_holds` takes of the storage package (each a linked `wp_proof` of `storage/`). -/
def walStorSpecs (h : WalH GF) : Prop :=
  letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj; haveI := h.sat; haveI := h.satL
  storage.storage.Save.spec (GF := GF) (Sio := h.Sio) walSrvP walSrvMr ∧
    storage.storage.SaveSnap.spec (GF := GF) (Sio := h.Sio) walSrvP walSrvMr ∧
    storage.storage.Sync.spec (GF := GF) (Sio := h.Sio) walSrvP walSrvMr ∧
    storage.storage.Close.spec (GF := GF) (Sio := h.Sio) walSrvP walSrvMr ∧
    storage.storage.Release.spec (GF := GF) (Sio := h.Sio) walSrvP walSrvMr

/-- **`Sync`'s law** from the storage's `Sync` (no error under `h.cov`; the length bound at `0` from the
share). -/
theorem walSync_law (h : WalH GF) (hS : walStorSpecs h) (p ss : Loc) (q : Qp) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ storage.storageOver p h.w ss ⊢
      {{ storage.walOpen h q ∗
          walStorRd (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p) h }}
        (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) go!"Sync" #p))
          (Val #()))
      {{ (err : GoInterface), RET #err; storage.walOpen h q ∗
          walStorRd (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p) h }} := by
  letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj; haveI := h.sat; haveI := h.satL
  obtain ⟨-, -, hSync, -, -⟩ := hS
  iintro ⟨#Hpkg, #Hover⟩
  iintro !> %Φ ⟨Ho, Hrd⟩ HΦ
  iunfold storage.walOpen at Ho
  icases Ho with ⟨Hws, #Harea, #Hlen⟩
  iunfold walStorRd at Hrd
  icases Hrd with ⟨%p', %Hp', Hrd⟩
  have hp : p' = p := by
    have := ((interface_mkOk_inj _ _ _ _).1 Hp').2
    exact (go.intoVal_inj this).symm
  subst hp
  wp_apply (hSync p' ss h.R h.jr h.r h.w h.dir h.γ q 0) $$ [Hrd Hws] as %err ⟨Hrd, Hpost⟩
  · iframe Hover Hrd Harea Hws Hlen
    ipureintro; exact Or.inl h.cov
  icases Hpost with (⟨-, Hws, -⟩ | %Hbad)
  · iapply HΦ
    iunfold storage.walOpen
    iframe Hws Harea Hlen
    iunfold walStorRd
    iexists p'
    iframe Hrd
    ipureintro; rfl
  · exact absurd h.cov Hbad.2

/-- The frozen entry contents, as the server's codec's entry objects (their wraps). -/
theorem walEntsIn_of_entRoC (esL : List Loc) (cs : List EntryC)
    (hc : ∀ c ∈ cs, ufWire entrySchema c.uf ∧ 0 < entrySize c ∧ entrySize c < 2 ^ 48) :
    ([∗list] l; c ∈ esL; cs, entRoC l c) ⊢ WalFs.walEntsIn (GF := GF) walSrvP esL (cs.map walEntW) := by
  unfold WalFs.walEntsIn
  refine (BigSepL2.bigSepL2_mono ?_).trans (BigSepL2.bigSepL2_map_right walEntW).2
  intro k l c _ hk
  have hcm := List.mem_of_getElem? hk
  show entRoC l c ⊢ walEntInW l (walEntW c)
  iintro #H
  unfold walEntInW
  iexists c
  iframe H
  ipureintro; exact ⟨rfl, hc c hcm⟩

/-- The bytes `Save`'s pre-lock check counts for wrapped contents (fix 0009): each content's encoding plus 64. -/
theorem saveBatchBytes_walEntW (cs : List EntryC)
    (hc : ∀ c ∈ cs, ufWire entrySchema c.uf ∧ 0 < entrySize c ∧ entrySize c < 2 ^ 48) :
    saveBatchBytes walSrvMr (cs.map walEntW) = (cs.map (fun c => entrySize c + 64)).sum := by
  unfold saveBatchBytes
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hcm
  show (walEncEntW (walEntW c)).length + 64 = entrySize c + 64
  rw [walEncEntW_W (hc c hcm).1 (hc c hcm).2.1 (hc c hcm).2.2, (walEntW_enc (hc c hcm).1 (hc c hcm).2.2).2]

/-- **`Save`'s law** from the storage's `Save` (the records' update as layer 1's, `walRecs_saveAU`; no I/O
error under `h.cov`). A batch above `MaxSaveBatchBytes` (fork fix 0009) is refused with the share, the token
and the update back: split on the batch's size first, the update passed to layer 1 only for a batch that
fits (where the refusal is impossible); for a larger one, layer 1's update is vacuous (its `Q` false, so its
other arms are impossible) and the caller's stays here. -/
theorem walSave_law (h : WalH GF) (hS : walStorSpecs h) (p ss : Loc) (sized : Bool) (q : Qp) (hp : Loc)
    (hs : HardStateM) (sl : GoSlice) (esL : List Loc) (cs : List EntryC) (Q : WalHist → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ storage.storageOver p h.w ss ⊢
      {{ storage.walOpen h q ∗
          walStorRd (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p) h ∗
          hsOptC hp hs ∗ sl ↦*□ esL ∗ ([∗list] l; c ∈ esL; cs, entRoC l c) ∗ ⌜∀ c ∈ cs, walSaveEntOk sized c⌝ ∗
          AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
            @ WalFs.walAuMask, ∅
            <{ walRecsH h (walSave σ hs (cs.map EntryC.model))
                (Hs ++ [WalOpG.save hs (cs.map EntryC.model)]) sized, COMM Q Hs }> }}
        (App (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) go!"Save" #p))
          (Val #hp)) (Val #sl))
      {{ (err : GoInterface), RET #err;
          (⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗
            walStorRd (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p) h ∗
            ∃ Hs : WalHist, Q Hs ∗
              (⌜walMustSync Hs hs (cs.map EntryC.model)⌝ -∗
                (letI := h.W; WalFs.walSyncedLb h.dir (Hs.length + 1)))) ∨
          (⌜err ≠ GoInterface.nil ∧ maxSaveBatch < (cs.map (fun c => entrySize c + 64)).sum⌝ ∗
            storage.walOpen h q ∗
            walStorRd (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p) h ∗
            AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                  ⌜WalSaveOk σ (cs.map EntryC.model)⌝ }>
              @ WalFs.walAuMask, ∅
              <{ walRecsH h (walSave σ hs (cs.map EntryC.model))
                  (Hs ++ [WalOpG.save hs (cs.map EntryC.model)]) sized, COMM Q Hs }>) }} := by
  letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj; haveI := h.sat; haveI := h.satL
  obtain ⟨hSave, -, -, -, -⟩ := hS
  iintro ⟨#Hpkg, #Hover⟩
  iintro !> %Φ ⟨Ho, Hrd, #Hhs, #Hsl, #Hb, %hc, HAU⟩ HΦ
  iunfold storage.walOpen at Ho
  icases Ho with ⟨Hws, #Harea, #Hlen⟩
  iunfold walStorRd at Hrd
  icases Hrd with ⟨%p', %Hp', Hrd⟩
  have hp' : p' = p := by
    have := ((interface_mkOk_inj _ _ _ _).1 Hp').2
    exact (go.intoVal_inj this).symm
  subst hp'
  have hc' : ∀ c ∈ cs, ufWire entrySchema c.uf ∧ 0 < entrySize c ∧ entrySize c < 2 ^ 48 :=
    fun c hcm => ⟨(hc c hcm).1, (hc c hcm).2.1, by have := (hc c hcm).2.2.1; omega⟩
  have hbytes := saveBatchBytes_walEntW cs hc'
  have hhs : (hsOptC hp hs : IProp GF) ⊢ (walSrvP (GF := GF)).hsIn hp hs := walHsIn_of_hsOptC hp hs
  ihave #Hhs' := hhs $$ Hhs
  ihave #Hes := walEntsIn_of_entRoC esL cs hc' $$ Hb
  have hidx : ∀ e ∈ cs.map walEntW, uint.nat e.Index' < 2 ^ 64 - 1 := by
    intro e he
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp he
    exact (hc c hcm).2.2.2.2
  have hsz : ∀ e ∈ cs.map walEntW, (walSrvMr.encEntry e).length < 2 ^ 40 := by
    intro e he
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp he
    show (walEncEntW (walEntW c)).length < 2 ^ 40
    rw [walEncEntW_W (hc' c hcm).1 (hc' c hcm).2.1 (hc' c hcm).2.2,
      (walEntW_enc (hc' c hcm).1 (hc' c hcm).2.2).2]
    exact (hc c hcm).2.2.1
  by_cases hfit : saveBatchBytes walSrvMr (cs.map walEntW) ≤ maxSaveBatch
  · -- the batch fits: the update passed down, the refusal impossible
    ihave HAU := walRecsH_saveAU h sized hs cs Q
      (fun c hcm => ⟨(hc c hcm).1, by have := (hc c hcm).2.2.1; omega, (hc c hcm).2.2.2.1⟩) $$ HAU
    wp_apply (hSave p' ss h.R h.jr h.r h.w h.dir h.γ q hp hs sl esL (cs.map walEntW) true
        (fun d => Q (walSrvHist d.H)))
      $$ [Hrd Hws HAU] as %err ⟨Hrd, Hpost⟩
    · iframe Hover Hrd Harea Hws Hsl
      isplitr
      · ipureintro; exact Or.inl h.cov
      isplitr
      · ipureintro; exact fun _ => ⟨h.fits, h.covP⟩
      isplitr
      · iexact Hhs'
      isplitr
      · iexact Hes
      isplitr
      · ipureintro; exact hidx
      isplitr
      · ipureintro; exact hsz
      · iintro %_
        iexact HAU
    icases Hpost with (⟨%he, Hws, %d, HQ, -, Hsync⟩ | ⟨%Hbad, -⟩ | ⟨%Hbig, -⟩)
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; exact he
      isplitl [Hws]
      · iunfold storage.walOpen
        iframe Hws Harea Hlen
      isplitl [Hrd]
      · iunfold walStorRd
        iexists p'
        iframe Hrd
        ipureintro; rfl
      iexists walSrvHist d.H
      iframe HQ
      iintro %hm
      rw [walSrvHist_length]
      iapply Hsync
      ipureintro; exact walMustSync_srv d.H hs cs hm
    · exact absurd h.cov Hbad.2
    · exfalso; have := Hbig.2; omega
  · -- too large: layer 1's update vacuous, the caller's kept
    wp_apply (hSave p' ss h.R h.jr h.r h.w h.dir h.γ q hp hs sl esL (cs.map walEntW) true
        (fun _ => iprop(False))) $$ [Hrd Hws] as %err ⟨Hrd, Hpost⟩
    · iframe Hover Hrd Harea Hws Hsl
      isplitr
      · ipureintro; exact Or.inl h.cov
      isplitr
      · ipureintro; exact fun _ => ⟨h.fits, h.covP⟩
      isplitr
      · iexact Hhs'
      isplitr
      · iexact Hes
      isplitr
      · ipureintro; exact hidx
      isplitr
      · ipureintro; exact hsz
      · iintro %hle
        exact absurd hle hfit
    icases Hpost with (⟨-, -, %d, HF, -, -⟩ | ⟨-, %d, HF⟩ | ⟨%Hbig, Hws⟩)
    · icases HF with %hF; exact hF.elim
    · icases HF with %hF; exact hF.elim
    · iapply HΦ
      iright
      iframe HAU
      isplitr
      · ipureintro; exact ⟨Hbig.1, by rw [← hbytes]; exact Hbig.2⟩
      isplitl [Hws]
      · iunfold storage.walOpen
        iframe Hws Harea Hlen
      · iunfold walStorRd
        iexists p'
        iframe Hrd
        ipureintro; rfl

/-- **`SaveSnap`'s law** from the storage's `SaveSnap` (the records' update as layer 1's,
`walRecs_saveSnapAU`; the record's bytes the canonical ones, F2; the synced record's witness from the
history's lower bound and the synced mark). -/
theorem walSaveSnap_law (h : WalH GF) (hS : walStorSpecs h) (p ss : Loc) (sized : Bool) (q : Qp)
    (sn mp : Loc) (dq : DFrac) (m : SnapMetaC) (al : Bool) (Q : WalHist → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ storage.storageOver p h.w ss ⊢
      {{ storage.walOpen h q ∗
          walStorRd (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p) h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ metaRoC mp m ∗
          ⌜m.index.isSome ∧ m.term.isSome ∧ storage.metaWalC m = walSnapCanon m.model al⌝ ∗
          ⌜m.model.Index' = W64 0 ∨ m.confState.isSome = true⌝ ∗
          ⌜uint.nat m.model.Index' < 2 ^ 64 - 1 ∧ (walSrvMr.encSnap m.model al).length < 2 ^ 40⌝ ∗
          AU <{ ∃∃ (σ : StorContents) (Hs : WalHist), walRecsH h σ Hs sized ∗
                ⌜uint.nat m.model.Index' = σ.b → m.model.Term' = σ.base.term'⌝ }>
            @ WalFs.walAuMask, ∅
            <{ walRecsH h (walSaveSnap σ m.model) (Hs ++ [WalOpG.snap m.model al]) sized,
              COMM Q Hs }> }}
        (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) go!"SaveSnap" #p))
          (Val #sn))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ storage.walOpen h q ∗
          walStorRd (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p) h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗
          ∃ Hs : WalHist, Q Hs ∗ (letI := h.W; WalFs.walSyncedLb h.dir (Hs.length + 1)) ∗
            walSnapRec h Hs.length m.model }} := by
  letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj; haveI := h.sat; haveI := h.satL
  obtain ⟨-, hSnap, -, -, -⟩ := hS
  iintro ⟨#Hpkg, #Hover⟩
  iintro !> %Φ ⟨Ho, Hrd, Hsn, #Hm, %hm1, %hm2, %hm3, HAU⟩ HΦ
  iunfold storage.walOpen at Ho
  icases Ho with ⟨Hws, #Harea, #Hlen⟩
  iunfold walStorRd at Hrd
  icases Hrd with ⟨%p', %Hp', Hrd⟩
  have hp' : p' = p := by
    have := ((interface_mkOk_inj _ _ _ _).1 Hp').2
    exact (go.intoVal_inj this).symm
  subst hp'
  ihave HAU := walRecsH_saveSnapAU h sized m.model al Q $$ HAU
  wp_apply (hSnap p' ss h.R h.jr h.r h.w h.dir h.γ q sn mp dq m al true
      (fun d => iprop(Q (walSrvHist d.H) ∗ monoListLbOwn h.γh (d.H ++ [WalOpG.snap m.model al]))))
    $$ [Hrd Hws HAU Hsn] as %err ⟨Hrd, Hsn, Hpost⟩
  · iframe Hover Hrd Harea Hws Hsn Hm HAU
    isplitr
    · ipureintro; exact ⟨hm1.1, hm1.2.1⟩
    isplitr
    · ipureintro
      show WalEnc.snapEnc (storage.metaWalC m) = WalEnc.snapEnc (walSnapCanon m.model al)
      rw [hm1.2.2]
    isplitr
    · ipureintro; exact Or.inl h.cov
    isplitr
    · ipureintro; exact fun _ => ⟨h.fits, h.covP⟩
    isplitr
    · ipureintro; exact hm2
    isplitr
    · ipureintro; exact hm3.1
    · ipureintro; exact hm3.2
  icases Hpost with (⟨%he, Hws, %d, ⟨HQ, #Hlb⟩, -, #Hsy⟩ | ⟨%Hbad, -⟩)
  · ihave #Hrec := walSnapRec_intro h d.H m.model al $$ [Hlb Hsy]
    · iframe Hlb Hsy
    iapply HΦ
    iframe Hsn
    isplitr
    · ipureintro; exact he
    isplitl [Hws]
    · iunfold storage.walOpen
      iframe Hws Harea Hlen
    isplitl [Hrd]
    · iunfold walStorRd
      iexists p'
      iframe Hrd
      ipureintro; rfl
    · iexists walSrvHist d.H
      rw [walSrvHist_length]
      iframe HQ Hsy Hrec
  · exact absurd h.cov Hbad.2

/-- **`Release`'s law** from the storage's `Release` (the records read, layer 1's lock update at the
snapshot record the witness names, `walRecs_releaseAU`). -/
theorem walRelease_law (h : WalH GF) (hS : walStorSpecs h) (p ss : Loc) (q : Qp) (sn mp : Loc)
    (dq dq' : DFrac) (md : SnapshotMetadataM) (sd : GoString) (γd : GName)
    (img : w64 → backend.Data → IProp GF)
    (Rm : w64 → IProp GF) (i : Nat) (m : SnapshotMetadataM) (Q : IProp GF) (hm : m.Index' = md.Index') :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ storage.storageOver p h.w ss ⊢
      {{ storage.walOpen h q ∗
          walStorRd (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p) h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗
          snap.isSnapshotter ss sd ∗ snapDirInvH sd γd img Rm ∗
          □ (∀ j : w64, ⌜uint.Z j < uint.Z md.Index'⌝ -∗ Rm j) ∗
          walSnapRec h i m ∗
          AU <{ ∃∃ (σ : StorContents) (s : Bool), walRecs h σ s }> @ WalFs.walAuMask, ∅
            <{ walRecs h σ s, COMM Q }> }}
        (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) go!"Release" #p))
          (Val #sn))
      {{ (err : GoInterface), RET #err; storage.walOpen h q ∗
          walStorRd (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p) h ∗
          sn.[go_etcd_io.raft.v3.raftpb.Snapshot, go!"Metadata"] ↦{dq} mp ∗ smOpt mp dq' md ∗ Q ∗
          ⌜err = GoInterface.nil ∨ ¬ snap.dirReadOk ss⌝ }} := by
  letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj; haveI := h.sat; haveI := h.satL
  obtain ⟨-, -, -, -, hRel⟩ := hS
  have hau := walRecs_releaseAU h i m Q
  rw [hm] at hau
  iintro ⟨#Hpkg, #Hover⟩
  iintro !> %Φ ⟨Ho, Hrd, Hsn, Hsm, #Hss, #Hinv, #HRm, #Hw, HAU⟩ HΦ
  iunfold storage.walOpen at Ho
  icases Ho with ⟨Hws, #Harea, #Hlen⟩
  iunfold walStorRd at Hrd
  icases Hrd with ⟨%p', %Hp', Hrd⟩
  have hp' : p' = p := by
    have := ((interface_mkOk_inj _ _ _ _).1 Hp').2
    exact (go.intoVal_inj this).symm
  subst hp'
  ihave #Hsy := walSnapRec_synced h i m $$ Hw
  ihave HAU := hau $$ [HAU]
  · iframe Hw HAU
  wp_apply (hRel p' ss h.R h.jr h.r h.w h.dir h.γ q sn mp dq dq' md sd γd img Rm m.Term' i (i + 1)
      m.ConfState' (fun _ => Q)) $$ [Hrd Hws HAU Hsn Hsm] as %err ⟨Hrd, Hsn, Hsm, Hws, ⟨%d, HQ⟩, %he⟩
  · iframe Hover Hrd Hss Hsn Hsm Hinv HRm Harea Hws Hsy HAU
  iapply HΦ
  iframe HQ Hsn Hsm
  isplitl [Hws]
  · iunfold storage.walOpen
    iframe Hws Harea Hlen
  isplitl [Hrd]
  · iunfold walStorRd
    iexists p'
    iframe Hrd
    ipureintro; rfl
  · ipureintro; exact he

/-- **`Close`'s law** from the storage's `Close` (the records read, `walRecs_closeAU`; no error under
`h.cov`): the WAL's files. -/
theorem walClose_law (h : WalH GF) (hS : walStorSpecs h) (p ss : Loc) (sized : Bool) (σ : StorContents)
    (id cid : w64) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ storage.storageOver p h.w ss ⊢
      {{ storage.walOpen h 1 ∗ walRecs h σ sized ∗ walMetaIs h id cid ∗ walPurgeRight h ∗ ⌜σ.b ≤ σ.commit⌝ }}
        (App (Val #(methods (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) go!"Close" #p))
          (Val #()))
      {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ walFiles h.toWalA id cid σ sized }} := by
  letI := h.ext; letI := h.semOk; letI := h.has; letI := h.W; letI := h.inj; haveI := h.sat; haveI := h.satL
  obtain ⟨-, -, -, hClose, -⟩ := hS
  iintro ⟨#Hpkg, #Hover⟩
  iintro !> %Φ ⟨Ho, Hr, #Hmd, Hpr, %hb⟩ HΦ
  iunfold storage.walOpen at Ho
  icases Ho with ⟨Hws, #Harea, -⟩
  iunfold walPurgeRight at Hpr
  ihave HAU := walRecs_closeAU h σ sized id cid hb $$ [Hr]
  · iframe Hr Hmd
  wp_apply (hClose p ss h.R h.jr h.r h.w h.dir h.γ _) $$ [Hws Hpr HAU] as %err Hpost
  · iframe Hover Harea Hws Hpr HAU
  icases Hpost with (⟨%he, %d, Hf, #Hsy, Hu, Hp⟩ | %Hbad)
  · iapply HΦ
    isplitr
    · ipureintro; exact he h.cov
    · iapply Hf
      iframe Hsy Hu Hp
  · exact absurd h.cov Hbad.2

/-- **`NewStorage`'s contract** (`rnNewStorageOk`, wal-link L3): `NewStorage` gives the storage's facts
(`storageOver`) and two reader tokens; each of the contract's laws is the storage method's (`walSave_law`, ...,
under `hS`), with the snapshotter for `Release`. -/
theorem rnNewStorageOk_holds (wpNew : storage.NewStorage.spec (GF := GF) (hG := hG))
    (hS : ∀ h : WalH GF, walStorSpecs h) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ⊢ rnNewStorageOk := by
  iintro #Hpkg
  unfold rnNewStorageOk
  iintro !> %lg %ss %sd %h
  iintro !> %Φ #Hss HΦ
  wp_apply (wpNew lg h.w ss) as %p ⟨#Hover, Hr1, Hr2⟩
  iapply HΦ
  isplitr
  · iapply (isWalStorage_intro
      iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
        storage.storageOver p h.w ss ∗ snap.isSnapshotter ss sd)
      _ h ss (interface.mk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty) #p) rfl p rfl
      (by iintro ⟨-, #H2, -⟩; iunfold storage.storageOver at H2; icases H2 with ⟨#Hs, -⟩; iexact Hs)
      (fun sized q hp hs sl esL cs Q => by
        iintro ⟨#H1, #H2, -⟩
        iapply (walSave_law h (hS h) p ss sized q hp hs sl esL cs Q)
        iframe H1 H2)
      (fun sized q sn mp dq m al Q => by
        iintro ⟨#H1, #H2, -⟩
        iapply (walSaveSnap_law h (hS h) p ss sized q sn mp dq m al Q)
        iframe H1 H2)
      (fun q => by
        iintro ⟨#H1, #H2, -⟩
        iapply (walSync_law h (hS h) p ss q)
        iframe H1 H2)
      (fun q sn mp dq dq' md sd' γd img Rm i m Q => by
        iintro ⟨#H1, #H2, -⟩ %hm
        iapply (walRelease_law h (hS h) p ss q sn mp dq dq' md sd' γd img Rm i m Q hm)
        iframe H1 H2)
      (fun sized σ id cid => by
        iintro ⟨#H1, #H2, -⟩
        iapply (walClose_law h (hS h) p ss sized σ id cid)
        iframe H1 H2))
    iframe Hpkg Hover Hss
  isplitl [Hr1]
  · iunfold walStorRd; iexists p; iframe Hr1; ipureintro; rfl
  · iunfold walStorRd; iexists p; iframe Hr2; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
