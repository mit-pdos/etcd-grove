/- Lean-first (no Rocq counterpart).

# The crash-aware durability invariant's steps, proved (etcd-dist D6, task T2 / P5, 2026-11-25)

Proofs of `InvWalCrash.lean`'s step laws (the crash's is `InvWalCrashLaws.lean`'s): the loop's `Save`
(`rnDurK_save_law_holds`), the received snapshot's `SaveSnap` (`rnDurK_saveSnap_law_holds`), the
*enter* (`rnDurK_enter_law_holds`), the apply thread's own `SaveSnap` (`rnDurK_ownSnap_law_holds`), the
stop's take (`rnDurK_take_law_holds`) and the allocation (`rnDurK_alloc_law_holds`), over the pure
steps of `InvWalCrashPure.lean`. Each opens the invariant at the WAL's client mask, strips the later
of the timeless rows, and keeps raft's side (`raftState`, the pending batch's *enter*) under it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWalCrashPure
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWalCrashLaws

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem rnPendK_none (γn : SrvRaft) (id : w64) (x : CrashNames) (v : WalView) :
    rnPendK (GF := GF) γn id x (v, none) = iprop(True) := rfl

theorem walHistCerts_snoc (cl : Cluster) (sd : w64 → IProp GF) (Hs : WalHist) (o : WalOp) :
    walHistCerts (GF := GF) cl sd Hs ∗ walOpCert cl sd o ⊢ walHistCerts cl sd (Hs ++ [o]) := by
  iintro ⟨#Hc, #Ho⟩
  iunfold walHistCerts at Hc
  iunfold walHistCerts
  iapply (BigSepL.bigSepL_snoc (Φ := fun _ (o : WalOp) => walOpCert (GF := GF) cl sd o)).2
  isplitl
  · iexact Hc
  · iexact Ho

/-- (P5-RESTART, option (B)) **A record that keeps or raises the last saved commit extends the body's
certificates**, given its own (`walOpCert`). -/
theorem walHistCertsK_snoc (cl : Cluster) (sd : w64 → IProp GF) (Hs : WalHist) (n : Nat) (o : WalOp)
    (hle : uint.nat (walLastHS Hs).Commit' ≤ uint.nat (walLastHS (Hs ++ [o])).Commit') :
    walHistCertsK (GF := GF) cl sd Hs n ∗ walOpCert cl sd o ⊢ walHistCertsK cl sd (Hs ++ [o]) n := by
  iintro ⟨#Hk, #Ho⟩
  iunfold walHistCertsK at Hk
  icases Hk with ⟨%σ0, %k, %Hb, #Hc0, #Hd0, #Hc⟩
  obtain ⟨hkn, hb⟩ := Hb
  have hk : k ≤ Hs.length := hb.1
  ihave #Hc' := walHistCerts_snoc cl sd (Hs.drop k) o $$ [Hc Ho]
  · iframe Hc Ho
  iunfold walHistCertsK
  iexists σ0, k
  rw [List.drop_append_of_le_length hk]
  iframe Hc0 Hd0 Hc'
  ipureintro
  exact ⟨hkn, certBaseK_snoc o hb hle⟩

/-- (P5-RESTART, option (B)) The body's certificates at a higher synced lower bound. -/
theorem walHistCertsK_mono (cl : Cluster) (sd : w64 → IProp GF) (Hs : WalHist) (n n' : Nat)
    (hn : n ≤ n') : walHistCertsK (GF := GF) cl sd Hs n ⊢ walHistCertsK cl sd Hs n' := by
  iintro #Hk
  iunfold walHistCertsK at Hk
  icases Hk with ⟨%σ0, %k, %Hb, #Hc0, #Hd0, #Hc⟩
  iunfold walHistCertsK
  iexists σ0, k
  iframe Hc0 Hd0 Hc
  ipureintro
  exact ⟨Nat.le_trans Hb.1 hn, Hb.2⟩

/-- (P5-RESTART, option (B)) **The body's certificates at an allocation**: from the records `σ` the whole
history reads as (`HistReads`), certified, the base at the history's end (no record after it). -/
theorem walHistCertsK_alloc (cl : Cluster) (sd : w64 → IProp GF) (Hs : WalHist) (σ : StorContents)
    (hr : HistReads σ Hs) :
    walSnapCert (GF := GF) cl σ ∗ walSnapDur sd σ ⊢ walHistCertsK cl sd Hs Hs.length := by
  iintro ⟨#Hc0, #Hd0⟩
  iunfold walHistCertsK
  iexists σ, Hs.length
  rw [List.drop_length]
  iframe Hc0 Hd0
  isplitr
  · ipureintro; exact ⟨Nat.le_refl _, certBaseK_restart hr⟩
  iunfold walHistCerts; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial

/-- (P5-RESTART, option (B)) **A restart's records have the snapshot of no data, or none** (their read's,
`walRead_snapSrc`): so with a trivial durability (`bootstrappedRaft.newRaftNode`'s `sd`) their snapshot is
durable. -/
theorem rnRestartWal_snapDurTriv (h : WalH GF) (σ : StorContents) :
    rnRestartWal h σ ⊢ rnRestartWal h σ ∗ walSnapDur (fun _ => iprop(True)) σ := by
  iintro Hw
  iunfold rnRestartWal at Hw
  icases Hw with ⟨%Hs, Hr, #Hsy, %Hp⟩
  have hrd : walRead Hs = some σ := by
    rw [walRead_eq_at]; exact (Hp.2 _ (Nat.le_refl _)).1
  isplitl [Hr]
  · iunfold rnRestartWal
    iexists Hs
    iframe Hr Hsy
    ipureintro; exact Hp
  iunfold walSnapDur
  rcases walRead_snapSrc hrd with ⟨-, hn⟩ | ⟨m, -, -, hsn, -⟩
  · ileft; ipureintro; exact hn
  · iright; iexists m
    isplitr
    · ipureintro; exact hsn
    imodintro; itrivial

/-- **The loop's `Save`** (`rnDurK_save.law`). -/
theorem rnDurK_save_law_holds : rnDurK_save.law (GF := GF) := by
  intro γn id νk h v v' hs es γb nd st st' ms q Hst Hda Hidx Hcl Hcmono
  obtain ⟨Hpn, Hpfx, Hstep⟩ := Hst
  iintro #Hinv Hvw #Hl' #Hsp Hrec
  iunfold rnWalViewK at Hvw
  icases Hvw with ⟨Hv, Hok⟩
  iauintro
  unfold atomic_acc
  iunfold rnDurInvK at Hinv
  icases Hinv with ⟨-, #Hinv⟩
  iinv Hinv with Hi Hclose
  all_goals first | exact rnDurKN_sub_walAuMask | skip
  icases Hi with (Hb | ⟨>Hs', >Ha', >Hok', >Htn'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Hok Hok'
  iunfold rnDurBodyK at Hb
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%vk, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%σ, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%Hs, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%n, Hb⟩
  icases Hb with ⟨>Hv0, >Hcm, >Htn, >Hr, #Hsc, #Hsy, #Hhc, #Hlb, >%Hp, Hraft⟩
  icombine Hv Hv0 gives %Hag
  have Hvv : (v, none) = vk := Hag.2
  subst Hvv
  obtain ⟨Hview, -, Hho, Hrk⟩ := Hp
  obtain ⟨Hsok, Hview'⟩ := Hstep σ Hview
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  have hlast : walLastHS Hs = v.hs := by rw [histReadsK_hs Hrk, Hview.2.1]
  iexists Hs
  iframe Hr
  isplit
  · iintro Hr
    imod Hmask with -
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
    · inext; ileft; iunfold rnDurBodyK
      iexists (v, none), σ, Hs, n
      iframe Hv0 Hcm Htn Hr Hsc Hsy Hhc Hlb Hraft
      ipureintro; exact ⟨Hview, fun _ _ _ hp => by simp at hp, Hho, Hrk⟩
    imodintro
    iframe Hv Hok Hrec
  · iintro Hr
    imod Hmask with -
    let vk' : WalViewK := (v', some (v, γb, Hs.length))
    imod (ghostVar_update_halves vk' νk.ν.view (v, none) (v, none)) $$ Hv Hv0 with ⟨Hv, Hv0⟩
    imod (monoListAuthOwn_update (GF := GF) (γ := νk.ν.cm) v'.l Hpfx) $$ Hcm with ⟨Hcm, #Hcl'⟩
    have hr' : recsOf v' (walSave (recsOf v σ) hs es) = walSave (recsOf v σ) hs es := by
      unfold recsOf; rw [Hpn]
    have Hh' := Hview'.1
    have hb' : (walSave (recsOf v σ) hs es).b ≤ (walSave (recsOf v σ) hs es).commit := Hh'.2.2.2.2.2.1
    have hcl' := storageHolds_commit_le_last Hh' Hcl
    have Hrk' := histReads_save Hrk Hview Hpn Hsok Hview' hcl' (by rw [hlast]; exact Hcmono)
    obtain ⟨hrd', hcle'⟩ := histReadsK_read Hrk' Hview'
    have Hho' : HistOkK vk' (Hs ++ [WalOpG.save hs es]) n :=
      histOk_save Hho hrd' hcle' ⟨Hh', Hview'.2.2.1⟩ Hidx (by rw [hlast]; exact Hcmono)
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft Hrec] with -
    · inext; ileft; iunfold rnDurBodyK
      ihave #Hhc' := walHistCertsK_snoc γn.cl νk.sd Hs n (WalOpG.save hs es)
          (by rw [walLastHS_snoc_saveP, hlast]; exact Hcmono) $$ [Hhc]
      · iframe Hhc; simp only [walOpCert]; itrivial
      iexists vk', walSave (recsOf v σ) hs es, Hs ++ [WalOpG.save hs es], n
      rw [hr', walSnapCert_save]
      iframe Hv0 Hcm Htn Hr Hsc Hsy Hhc'
      isplitr
      · iunfold rnLogLbsK
        iunfold rnLogLbsK at Hlb
        icases Hlb with ⟨#Hl0, -⟩
        iframe Hl' Hl0
      isplitr
      · ipureintro
        exact ⟨Hview', fun v0 γ0 pos hp => by
          simp only [vk', Option.some.injEq, Prod.mk.injEq] at hp
          obtain ⟨rfl, -, -⟩ := hp; exact Hda, Hho', Hrk'⟩
      icases Hraft with (⟨HrS, -⟩ | Hc)
      · ileft
        simp only [vk', durOf]
        iframe HrS
        rw [rnPendK_some]
        iexists nd, st, st', ms, q
        iframe Hsp Hrec
      · iright; iexact Hc
    imodintro
    iunfold rnWalViewK
    iframe Hv Hok
    isplitr
    · iunfold walCommitLb; iexact Hcl'
    ipureintro
    exact ⟨⟨_, hrd'⟩, hlast⟩

/-- (P5) **The loop's idle view describes the records** (`rnDur_viewOk`'s, the crash-aware invariant): some
records `σ` it is within (`ViewOk`), the half given back. -/
theorem rnDurK_viewOk (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) (v : WalView) :
    ⊢ rnDurInvK γn id νk h -∗ rnWalViewK νk (v, none) ={⊤}=∗
      rnWalViewK νk (v, none) ∗ ⌜∃ σ, ViewOk v σ⌝ := by
  iintro #Hinv Hvw
  iunfold rnWalViewK at Hvw
  icases Hvw with ⟨Hv, Hok⟩
  iunfold rnDurInvK at Hinv
  icases Hinv with ⟨-, #Hinv⟩
  iinv Hinv with Hi Hclose
  icases Hi with (Hb | ⟨>Hs', >Ha', >Hok', >Htn'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Hok Hok'
  iunfold rnDurBodyK at Hb
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%vk, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%σ, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%Hs, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%n, Hb⟩
  icases Hb with ⟨>Hv0, >Hcm, >Htn, >Hr, #Hsc, #Hsy, #Hhc, #Hlb, >%Hp, Hraft⟩
  icombine Hv Hv0 gives %Hag
  have Hvv : (v, none) = vk := Hag.2
  subst Hvv
  imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
  · inext; ileft; iunfold rnDurBodyK
    iexists (v, none), σ, Hs, n
    iframe Hv0 Hcm Htn Hr Hsc Hsy Hhc Hlb Hraft
    ipureintro; exact Hp
  imodintro
  iunfold rnWalViewK
  iframe Hv Hok
  ipureintro; exact ⟨σ, Hp.1⟩

/-- (P5) **A read of the records, as the WAL contract's atomic update** (`rnDur_read_au`'s, the crash-aware
invariant; `walRelease_spec`): with the apply thread's token (which rules out the stop's taken state),
the records and their history read and left unchanged. -/
theorem rnDurK_read_au (γn : SrvRaft) (id : w64) (νk : WalNamesK GF) (h : WalH GF) :
    rnDurInvK γn id νk h -∗ token νk.ν.app -∗
      AU <{ ∃∃ (Hs : WalHist) (s : Bool), walHistH h Hs s }> @ WalFs.walAuMask, ∅
        <{ walHistH h Hs s, COMM token νk.ν.app }> := by
  iintro #Hinv Ha
  iauintro
  unfold atomic_acc
  iunfold rnDurInvK at Hinv
  icases Hinv with ⟨-, #Hinv⟩
  iinv Hinv with Hi Hclose
  all_goals first | exact rnDurKN_sub_walAuMask | skip
  icases Hi with (Hb | ⟨>Hs', >Ha', >Hok', >Htn'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Ha Ha'
  iunfold rnDurBodyK at Hb
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%vk, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%σ, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%Hs, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%n, Hb⟩
  icases Hb with ⟨>Hv0, >Hcm, >Htn, >Hr, #Hsc, #Hsy, #Hhc, #Hlb, >%Hp, Hraft⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists Hs, true
  iframe Hr
  isplit
  · iintro Hr
    imod Hmask with -
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
    · inext; ileft; iunfold rnDurBodyK
      iexists vk, σ, Hs, n
      iframe Hv0 Hcm Htn Hr Hsc Hsy Hhc Hlb Hraft
      ipureintro; exact Hp
    imodintro
    iframe Ha
  · iintro Hr
    imod Hmask with -
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
    · inext; ileft; iunfold rnDurBodyK
      iexists vk, σ, Hs, n
      iframe Hv0 Hcm Htn Hr Hsc Hsy Hhc Hlb Hraft
      ipureintro; exact Hp
    imodintro
    iframe Ha

theorem srvClusterN_rnDurKN : (↑srvClusterN : CoPset) ⊆ ⊤ \ ↑rnDurKN :=
  fun x h => mask_ndot_ne' nroot "raft_commit" "rnDurK" (by decide) x (srvClusterN_sub x h)

/-- **The received snapshot's `SaveSnap`** (`rnDurK_saveSnap.law`). -/
theorem rnDurK_saveSnap_law_holds : rnDurK_saveSnap.law (GF := GF) := by
  intro γn id νk h v m al Hst Hm61
  obtain ⟨Hpn, Hstep⟩ := Hst
  iintro #Hinv Hvw #Hsv #Hsd
  iunfold rnWalViewK at Hvw
  icases Hvw with ⟨Hv, Hok⟩
  iauintro
  unfold atomic_acc
  iunfold rnDurInvK at Hinv
  icases Hinv with ⟨-, #Hinv⟩
  iinv Hinv with Hi Hclose
  all_goals first | exact rnDurKN_sub_walAuMask | skip
  icases Hi with (Hb | ⟨>Hs', >Ha', >Hok', >Htn'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Hok Hok'
  iunfold rnDurBodyK at Hb
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%vk, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%σ, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%Hs, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%n, Hb⟩
  icases Hb with ⟨>Hv0, >Hcm, >Htn, >Hr, #Hsc, #Hsy, #Hhc, #Hlb, >%Hp, Hraft⟩
  icombine Hv Hv0 gives %Hag
  have Hvv : (v, none) = vk := Hag.2
  subst Hvv
  obtain ⟨Hview, -, Hho, Hrk⟩ := Hp
  obtain ⟨-, Hview1⟩ := Hstep σ Hview
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists Hs
  iframe Hr
  isplit
  · iintro Hr
    imod Hmask with -
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
    · inext; ileft; iunfold rnDurBodyK
      iexists (v, none), σ, Hs, n
      iframe Hv0 Hcm Htn Hr Hsc Hsy Hhc Hlb Hraft
      ipureintro; exact ⟨Hview, fun _ _ _ hp => by simp at hp, Hho, Hrk⟩
    imodintro
    iframe Hv Hok
  · iintro Hr
    have hr0 : recsOf v σ = σ := by unfold recsOf; rw [Hpn]
    rw [hr0]
    imod Hmask with -
    let v2 : WalView := { v with pend := some m }
    imod (ghostVar_update_halves ((v2, none) : WalViewK) νk.ν.view (v, none) (v, none)) $$ Hv Hv0
      with ⟨Hv, Hv0⟩
    have hab : uint.nat (walLastHS Hs).Commit' < uint.nat m.Index' := by
      have h1 := Hview1.2.2.2.2.2 m rfl
      simp only [StorContents.commit] at h1
      rw [histReadsK_hs Hrk]; exact h1
    have Hho' : HistOkK (v2, none) (Hs ++ [WalOpG.snap m al]) n :=
      histOk_snapAbove Hho hab rfl rfl Hm61
    have Hrk' : HistReadsK v2 σ (Hs ++ [WalOpG.snap m al]) := histReads_snapAbove Hrk Hpn
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
    · inext; ileft; iunfold rnDurBodyK
      ihave #Hhc' := walHistCertsK_snoc γn.cl νk.sd Hs n (WalOpG.snap m al)
          (by rw [walLastHS_snoc_snapP]; exact Nat.le_refl _) $$ [Hhc]
      · iframe Hhc; simp only [walOpCert]; iframe Hsv Hsd
      ihave #Hsc' := walSnapCert_saveSnap γn.cl σ m $$ [Hsc]
      · iframe Hsc Hsv
      iexists (v2, none), σ, Hs ++ [WalOpG.snap m al], n
      have hr2 : recsOf v2 σ = walSaveSnap σ m := by simp [recsOf, v2]
      simp only [hr2]
      have hl2 : rnLogLbsK (GF := GF) γn.cl (v2, none) = rnLogLbsK γn.cl (v, none) := rfl
      rw [hl2]
      iframe Hv0 Hcm Htn Hr Hsc' Hsy Hhc' Hlb
      isplitr
      · ipureintro; exact ⟨Hview1, fun _ _ _ hp => by simp at hp, Hho', Hrk'⟩
      have hd2 : durOf ((v2, none) : WalViewK) = durOf (v, none) := rfl
      have hp2 : rnPendK (GF := GF) γn id νk.x (v2, none) = rnPendK γn id νk.x (v, none) := rfl
      rw [hd2, hp2]
      iexact Hraft
    imodintro
    iunfold rnWalViewK
    iframe Hv Hok

/-- (P5 (b)) **The apply thread's own snapshot is a WAL step, the records moving** (`walOwnSnapStep` with
the records before a pending received snapshot moved too: the reads at the commits below it see the
snapshot): `walSaveSnap σ md` describes the view, and the records it describes are the old ones with the
snapshot applied. -/
theorem walOwnSnapStepK (v : WalView) (σ : StorContents) (md : SnapshotMetadataM)
    (l : List LogEntry) (e : LogEntry) (Hpfx : l <+: v.l) (Hpos : 0 < uint.nat md.Index')
    (He : l[uint.nat md.Index' - 1]? = some e) (Ht : e.term = md.Term') (Hv : ViewOk v σ) :
    recsOf v (walSaveSnap σ md) = walSaveSnap (recsOf v σ) md ∧ ViewOk v (walSaveSnap σ md) := by
  let v0 : WalView := { v with pend := none }
  have Hv0 : ViewOk v0 σ :=
    ⟨Hv.1, Hv.2.1, Hv.2.2.1, Hv.2.2.2.1, Hv.2.2.2.2.1, fun m hm => by simp [v0] at hm⟩
  obtain ⟨-, σ', hσ', hv'⟩ := walOwnSnapStep v0 σ md l e Hpfx Hpos He Ht Hv0
  have hσ'' : σ' = walSaveSnap σ md := by simpa [recsOf, v0] using hσ'
  subst hσ''
  have hlen : l.length ≤ v.l.length := Hpfx.length_le
  have hil : uint.nat md.Index' - 1 < l.length := (List.getElem?_eq_some_iff.1 He).1
  have hmc : uint.nat md.Index' ≤ σ.commit := by have := Hv.2.2.2.1; omega
  have hc2 : (walSaveSnap σ md).commit = σ.commit := by
    simp only [StorContents.commit, walSaveSnap_hs]
  refine ⟨?_, hv'.1, hv'.2.1, hv'.2.2.1, hv'.2.2.2.1, hv'.2.2.2.2.1, ?_⟩
  · cases hm : v.pend with
    | none => simp only [recsOf, hm]
    | some m =>
      obtain ⟨e1, e2⟩ := walSaveSnap_own_pend (σ := σ) (md := md) (m := m) Hv.1.2.2.2.2.2.1 hmc
        (Hv.2.2.2.2.2 m hm)
      simp only [recsOf, hm]
      rw [e1, e2]
  · intro m hm
    rw [hc2]; exact Hv.2.2.2.2.2 m hm

/-- **The apply thread's own `SaveSnap`** (`rnDurK_ownSnap.law`). -/
theorem rnDurK_ownSnap_law_holds : rnDurK_ownSnap.law (GF := GF) := by
  intro γn id νk h md l e al Hpos He Ht Hm61
  iintro #Hinv Ha #Hlbc #Hsv #Hsd
  iauintro
  unfold atomic_acc
  iunfold rnDurInvK at Hinv
  icases Hinv with ⟨-, #Hinv⟩
  iinv Hinv with Hi Hclose
  all_goals first | exact rnDurKN_sub_walAuMask | skip
  icases Hi with (Hb | ⟨>Hs', >Ha', >Hok', >Htn'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Ha Ha'
  iunfold rnDurBodyK at Hb
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%vk, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%σ, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%Hs, Hb⟩
  imod (later_exists_except0 (PROP := IProp GF)) $$ Hb with ⟨%n, Hb⟩
  icases Hb with ⟨>Hv0, >Hcm, >Htn, >Hr, #Hsc, #Hsy, #Hhc, #Hlb, >%Hp, Hraft⟩
  obtain ⟨Hview, Hpo, Hho, Hrk⟩ := Hp
  iunfold walCommitLb at Hlbc
  ihave %Hpv := mono_list_auth_lb_valid νk.ν.cm 1 vk.1.l l $$ Hcm Hlbc
  obtain ⟨Hσ', Hok1⟩ := walOwnSnapStepK vk.1 σ md l e Hpv.2 Hpos He Ht Hview
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists Hs
  iframe Hr
  isplit
  · iintro Hr
    imod Hmask with -
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
    · inext; ileft; iunfold rnDurBodyK
      iexists vk, σ, Hs, n
      iframe Hv0 Hcm Htn Hr Hsc Hsy Hhc Hlb Hraft
      ipureintro; exact ⟨Hview, Hpo, Hho, Hrk⟩
    imodintro
    iframe Ha
  · iintro Hr
    imod Hmask with -
    have hil : uint.nat md.Index' - 1 < l.length := (List.getElem?_eq_some_iff.1 He).1
    have He' : vk.1.l[uint.nat md.Index' - 1]? = some e := by
      obtain ⟨t, ht⟩ := Hpv.2
      rw [← ht, List.getElem?_append_left hil]; exact He
    have hlen : l.length ≤ vk.1.l.length := Hpv.2.length_le
    have hc : uint.nat md.Index' ≤ uint.nat (walLastHS Hs).Commit' := by
      rw [histReadsK_hs Hrk]
      have := Hview.2.2.2.1
      simp only [StorContents.commit] at this
      omega
    have Hho' : HistOkK vk (Hs ++ [WalOpG.snap md al]) n :=
      histOk_ownSnap Hho hc Hview.2.2.2.2.1 Hpos He' Ht Hm61
    have Hrk' : HistReadsK vk.1 (walSaveSnap σ md) (Hs ++ [WalOpG.snap md al]) :=
      histReads_ownSnap Hrk Hview hc
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
    · inext; ileft; iunfold rnDurBodyK
      ihave #Hhc' := walHistCertsK_snoc γn.cl νk.sd Hs n (WalOpG.snap md al)
          (by rw [walLastHS_snoc_snapP]; exact Nat.le_refl _) $$ [Hhc]
      · iframe Hhc; simp only [walOpCert]; iframe Hsv Hsd
      ihave #Hsc' := walSnapCert_saveSnap γn.cl _ md $$ [Hsc]
      · iframe Hsc Hsv
      iexists vk, walSaveSnap σ md, Hs ++ [WalOpG.snap md al], n
      rw [Hσ']
      iframe Hv0 Hcm Htn Hr Hsc' Hsy Hhc' Hlb Hraft
      ipureintro; exact ⟨Hok1, Hpo, Hho', Hrk'⟩
    imodintro
    iframe Ha

/-- **The loop's *enter*** (`rnDurK_enter.law`). -/
theorem rnDurK_enter_law_holds : rnDurK_enter.law (GF := GF) := by
  intro γn id νk h v v' γb pos nd st st' ms q
  letI := srvStor (GF := GF) γn
  iintro #Hinv Hnc Hlc1 Hlc2 Hvw #Hsp Hsync
  iunfold rnWalViewK at Hvw
  icases Hvw with ⟨Hv, Hok⟩
  iunfold rnDurInvK at Hinv
  icases Hinv with ⟨-, #Hinv⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  icases Hi with (Hb | ⟨Hs', Ha', Hok', Htn'⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Hok Hok'
  iunfold rnDurBodyK at Hb
  icases Hb with ⟨%vk, %σ, %Hs, %n, Hv0, Hcm, Htn, Hr, #Hsc, #Hsy, #Hhc, #Hlb, %Hp, Hraft⟩
  icombine Hv Hv0 gives %Hag
  have Hvv : (v', some (v, γb, pos)) = vk := Hag.2
  subst Hvv
  obtain ⟨Hview, -, Hho, Hrk⟩ := Hp
  have hlast : walLastHS Hs = v'.hs := by rw [histReadsK_hs Hrk, Hview.2.1]
  icases Hraft with (⟨HrS, Hpend⟩ | ⟨Hcr, -⟩)
  try dsimp only [durOf]
  rotate_left
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hcr
  rw [rnPendK_some]
  icases Hpend with ⟨%n0, %st0, %st0', %ms0, %q0, #Hsp0, Hrec0⟩
  ihave #Heq := saved_prop_agree γb DFrac.discard DFrac.discard _ _ $$ Hsp0 Hsp
  ihave Hrec : ▷ rnPendRec γn id νk.x v.S v'.S nd st st' ms q $$ [Hrec0]
  · inext
    ihave Hiff := internalEq_iff _ _ $$ Heq
    icases Hiff with ⟨Hiff, -⟩
    iapply Hiff $$ Hrec0
  imod lc_fupd_elim_later $$ Hlc2 Hrec with Hrec
  iunfold rnPendRec at Hrec
  icases Hrec with ⟨-, Hent, Hrun, %Hst⟩
  obtain ⟨Hst1, Hst2⟩ := Hst
  ihave HrS : raftState γn.cl id st.durable $$ [HrS]
  · rw [Hst1]; iexact HrS
  iunfold readyEnter at Hent
  icases Hent with ⟨Hent, -⟩
  iunfold readyEnterLive at Hent
  imod Hent $$ %(⊤ \ ↑rnDurKN) %q %srvClusterN_rnDurKN Hnc [HrS Hrun]
    with ⟨Hnc, HrS, Hrun, Hdrv, Hmsgs⟩
  · iframe HrS Hrun
  ihave HrS : raftState γn.cl id v'.S $$ [HrS]
  · rw [← Hst2]; iexact HrS
  imod (ghostVar_update_halves ((v', none) : WalViewK) νk.ν.view _ _) $$ Hv Hv0 with ⟨Hv, Hv0⟩
  icases Hsync with (#Hsy' | %Himp)
  · have Hho' : HistOkK (v', none) Hs (max n (pos + 1)) := histOk_enter Hho hlast (Or.inl rfl)
    ihave #Hhc' := walHistCertsK_mono γn.cl νk.sd Hs n (max n (pos + 1)) (Nat.le_max_left _ _) $$ Hhc
    imod Hclose $$ [Hv0 Hcm Htn Hr HrS] with -
    · inext; ileft; iunfold rnDurBodyK
      iexists (v', none), σ, Hs, max n (pos + 1)
      iframe Hv0 Hcm Htn Hr Hsc Hhc'
      isplitr
      · rcases Nat.le_total n (pos + 1) with hle | hle
        · rw [Nat.max_eq_right hle]; iexact Hsy'
        · rw [Nat.max_eq_left hle]; iexact Hsy
      isplitr
      · iunfold rnLogLbsK; iunfold rnLogLbsK at Hlb
        icases Hlb with ⟨#Hl, -⟩
        iframe Hl
      isplitr
      · ipureintro; exact ⟨Hview, fun _ _ _ hp => by simp at hp, Hho', Hrk⟩
      ileft; simp only [durOf]; iframe HrS
      rw [rnPendK_none]; itrivial
    imodintro
    iframe Hnc Hdrv Hmsgs Hrun
    iunfold rnWalViewK
    iframe Hv Hok
  · have Hho' : HistOkK (v', none) Hs n := histOk_enter Hho hlast (Or.inr ⟨rfl, Himp⟩)
    imod Hclose $$ [Hv0 Hcm Htn Hr HrS] with -
    · inext; ileft; iunfold rnDurBodyK
      iexists (v', none), σ, Hs, n
      iframe Hv0 Hcm Htn Hr Hsc Hhc Hsy
      isplitr
      · iunfold rnLogLbsK; iunfold rnLogLbsK at Hlb
        icases Hlb with ⟨#Hl, -⟩
        iframe Hl
      isplitr
      · ipureintro; exact ⟨Hview, fun _ _ _ hp => by simp at hp, Hho', Hrk⟩
      ileft; simp only [durOf]; iframe HrS
      rw [rnPendK_none]; itrivial
    imodintro
    iframe Hnc Hdrv Hmsgs Hrun
    iunfold rnWalViewK
    iframe Hv Hok

/-- **The stop's take** (`rnDurK_take.law`). -/
theorem rnDurK_take_law_holds : rnDurK_take.law (GF := GF) := by
  intro γn id νk h v Hpn
  iintro #Hinv Hnc Hlc Hst Hap Hvw
  iunfold rnWalViewK at Hvw
  icases Hvw with ⟨Hv, Hok⟩
  iunfold rnDurInvK at Hinv
  icases Hinv with ⟨-, #Hinv⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  icases Hi with (Hb | ⟨Hst', -, -, -⟩)
  rotate_left
  · iexfalso; iapply token_exclusive $$ Hst Hst'
  iunfold rnDurBodyK at Hb
  icases Hb with ⟨%vk, %σ, %Hs, %n, Hv0, -, Htn, Hr, #Hsc, -, -, -, %Hp, Hraft⟩
  icombine Hv Hv0 gives %Hag
  have Hvv : (v, none) = vk := Hag.2
  subst Hvv
  obtain ⟨Hview, -, -, Hrk⟩ := Hp
  icases Hraft with (⟨HrS, -⟩ | ⟨Hcr, -⟩)
  try dsimp only [durOf]
  rotate_left
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hcr
  imod dghostVar_persist νk.tkn 1 () $$ Htn with #Htn
  imod Hclose $$ [Hst Hap Hok] with -
  · inext; iright; iframe Hst Hap Hok Htn
  have hr : recsOf v σ = σ := by unfold recsOf; rw [Hpn]
  rw [hr] at *
  imodintro
  iframe Hnc HrS
  isplitr
  · iunfold rnTakenK; iexact Htn
  iexists σ
  rw [hr]
  iframe Hsc
  isplitl [Hr]
  · iapply walHistH_walRecs h σ Hs true
    iframe Hr; ipureintro; exact histReadsK_fold Hrk Hpn
  ipureintro
  obtain ⟨Hh, Hhs, Hb, Hc, Hag, -⟩ := Hview
  exact ⟨Hh, Hb, Hc, Hhs, Hag⟩

/-- **The allocation** (`rnDurK_alloc.law`). -/
theorem rnDurK_alloc_law_holds : rnDurK_alloc.law (GF := GF) := by
  intro γn id x sd h σ Hs n v Hv Hpn Hda Hho Hrd
  iintro Hr #Hsc #Hsy #Hhc #Hl HrS
  imod (ghostVar_alloc (GF := GF) ((v, none) : WalViewK)) with ⟨%γv, Hvw⟩
  imod (mono_list_own_alloc (GF := GF) v.l) with ⟨%γc, Hca, #Hcl⟩
  imod (token_alloc (GF := GF)) with ⟨%γo, Ho⟩
  imod (token_alloc (GF := GF)) with ⟨%γs, Hs'⟩
  imod (token_alloc (GF := GF)) with ⟨%γa, Ha⟩
  imod (token_alloc (GF := GF)) with ⟨%γk, Hk⟩
  imod (dghostVar_alloc (GF := GF) ()) with ⟨%γt, Ht⟩
  icases (ghostVar_split_half γv 1 ((v, none) : WalViewK)).1 $$ Hvw with ⟨Hv1, Hv2⟩
  let νk : WalNamesK GF := ⟨⟨h, γv, γc, γo, γs, γa⟩, γk, x, γt, sd⟩
  have hr : recsOf v σ = σ := by unfold recsOf; rw [Hpn]
  imod (inv_alloc rnDurKN ⊤ iprop(rnDurBodyK γn id νk h ∨
      (token νk.ν.stop ∗ token νk.ν.app ∗ token νk.ν.ok ∗ dghostVar νk.tkn DFrac.discard ())))
    $$ [Hv1 Hca Ht Hr HrS] with #Hinv
  · inext
    ileft
    iunfold rnDurBodyK
    iexists (v, none), σ, Hs, n
    rw [hr]
    iframe Hv1 Hca Ht Hr Hsc Hsy Hhc
    isplitr
    · iunfold rnLogLbsK; iframe Hl
    isplitr
    · ipureintro; exact ⟨Hv, fun _ _ _ hp => by simp at hp, Hho, histReadsK_of_none Hpn Hrd⟩
    ileft
    simp only [durOf]
    isplitl [HrS]
    · iexact HrS
    · iunfold rnPendK; itrivial
  imodintro
  iexists νk
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iunfold rnDurInvK
  iframe Hinv Hs' Ha Hk
  isplitr
  · ipureintro; rfl
  isplitl [Hv2 Ho]
  · iunfold rnWalViewK; iframe Hv2 Ho
  iunfold walCommitLb; iexact Hcl

/-- (P5) **The crash-aware durability's allocation at a first start** (`rnDurK_alloc.law` at `walFresh`,
the empty history, `walView0`): the invariant over the fresh records, raft's state at `RaftState.init`. -/
theorem rnDurK_alloc_fresh (γn : SrvRaft) (id : w64) (x : CrashNames) (sd : w64 → IProp GF) (h : WalH GF) :
    ⊢ walHistH h [] true -∗ raftState γn.cl id RaftState.init ={⊤}=∗
      ∃ νk : WalNamesK GF, ⌜νk.x = x ∧ νk.sd = sd ∧ νk.ν.h = h⌝ ∗ rnDurInvK γn id νk h ∗
        rnWalViewK νk (walView0, none) ∗ token νk.ν.stop ∗ token νk.ν.app ∗ walCommitLb νk.ν [] := by
  have hv : ViewOk walView0 walFresh :=
    ⟨walFresh_holds, rfl, Nat.le_refl _, Nat.zero_le _, fun i e _ he => by simp at he,
      fun m hm => by simp at hm⟩
  have hok : HistOkK (walView0, none) [] 0 := histOk_fresh ⟨hv.1, Nat.le_refl _⟩
  iintro Hr HrS
  icases walHistH_synced0 h _ _ $$ Hr with ⟨Hr, #Hsy⟩
  ihave #Hc := walSnapCert_fresh (GF := GF) γn.cl
  ihave #Hhc : walHistCertsK γn.cl sd [] 0 $$ []
  · iapply walHistCertsK_alloc γn.cl sd [] walFresh histReads_fresh
    iframe Hc
    iunfold walSnapDur; ileft; ipureintro; rfl
  ihave #Hl := isCommittedLogLb_nil (GF := GF) γn.cl
  imod rnDurK_alloc_law_holds γn id x sd h walFresh [] 0 walView0 hv rfl hv.2.2.2.2.1 hok histReads_fresh
    $$ Hr Hc Hsy Hhc Hl HrS with ⟨%νk, %Hx, #Hinv, Hv, Hst, Hap, #Hlb, -⟩
  ihave #Hinv' := Hinv
  iunfold rnDurInvK at Hinv'
  icases Hinv' with ⟨%Hh, -⟩
  imodintro
  iexists νk
  iframe Hinv Hv Hst Hap Hlb
  ipureintro; exact ⟨Hx.1, Hx.2, Hh⟩

/-- (P5, 2026-11-25) **What the restarted server takes from `wal.restartOk`** (`wal.restartOk_start`'s
crash-aware form): the open WAL `h` at `w`, the restart's handover of its records (`rnRestartWal`, for
the crash-aware durability `bootstrappedRaft.newRaftNode` allocates), the records within the restart's
view `⟨S, σ.hs, none, l₀⟩` (`viewOk_restart`: `l₀` committed, reaching the records' base, the durable
log of the stop image agreeing with it), the image's WAL slot given back, and what `NewStorage` and
`Close` take. -/
theorem wal.restartOk_startRK (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (id cid : w64)
    (w : Loc) (σ : StorContents) (cl : Cluster) (S : RaftState) (i : w64) (l₀ : List LogEntry)
    (hl : l₀.length = σ.b) :
    wal.restartOk (GF := GF) cfg id cid w σ ∗ wal.stopImage cl S σ i ∗ isCommittedLogLb cl l₀ ⊢
      ∃ h : WalH GF, ⌜h.w = w⌝ ∗ rnRestartWal h σ ∗ ⌜ViewOk ⟨S, σ.hs, none, l₀⟩ σ⌝ ∗
        wal.stopImage cl S σ i ∗ storage.walOpen h 1 ∗ walMetaIs h id cid ∗ walPurgeRight h ∗
        ⌜h.dir = cfg.DedicatedWALDir'⌝ := by
  iintro ⟨Hro, Hsi, #Hl0⟩
  icases wal.restartOk_startK cfg id cid w σ $$ Hro with ⟨%h, %Hs, %Hw, Hr, #Hsy, %Hp, Ho, Hm, Hpg, %Hd⟩
  obtain ⟨hidx, heag, hf, hrf⟩ := Hp
  have hrd : HistReads σ Hs := histReads_of_fold hf hrf.2.2.1 heag
  icases wal.stopImage_elim cl S σ i $$ Hsi with ⟨%HsI, #Hcert, ⟨%l', #Hl', %Hl'b, %Hag⟩⟩
  icases isCommittedLogLb_agree cl l₀ l' $$ [$Hl0 $Hl'] with %Hpre
  have hpre : l₀ <+: l' := by
    rcases Hpre with h | h
    · exact h
    · have := h.length_le
      have heq : l' = l₀ := h.eq_of_length (by omega)
      rw [heq]; exact List.prefix_refl _
  have hag0 : DurAgrees S l₀ := durAgrees_prefix S l₀ l' hpre Hag
  have hv : ViewOk ⟨S, σ.hs, none, l₀⟩ σ :=
    viewOk_restart S σ l₀ HsI.1 (by omega) (by rw [hl]; exact hrf.2.2.1) hag0
  ihave Hsi2 := wal.stopImage_intro cl S σ i HsI.1 HsI.2.1 HsI.2.2 $$ [Hcert Hl']
  · iframe Hcert
    iexists l'
    iframe Hl'
    ipureintro; exact ⟨Hl'b, Hag⟩
  iexists h
  isplitr
  · ipureintro; exact Hw
  isplitl [Hr]
  · iunfold rnRestartWal
    iexists Hs
    iframe Hr Hsy
    ipureintro; exact ⟨hidx, hrd⟩
  isplitr
  · ipureintro; exact hv
  iframe Hsi2 Ho Hm Hpg
  ipureintro; exact Hd

/-- (P5) **`rnRestartAllocK.law`** (the isolated restart step): `rnDurK_alloc.law` at the restart's
records, with `histOk_restart`. (P5-RESTART, option (B), 2026-11-26: until then a `sorry` for the
certificates of the restarted history's snapshot records, `walHistCerts`, which the restart slot does not
carry) The invariant's certificates start at the restarted history's end, from the restart read's own
certificate (`walHistCertsK_alloc`). -/
theorem rnRestartAllocK_law_holds : rnRestartAllocK.law (GF := GF) := by
  intro γn id x sd h σ S l₀ hv
  iintro Hw #Hc #Hd #Hl HrS
  iunfold rnRestartWal at Hw
  icases Hw with ⟨%Hs, Hr, #Hsy, %Hp⟩
  obtain ⟨hidx, hrd⟩ := Hp
  have hok : HistOkK ((⟨S, σ.hs, none, l₀⟩ : WalView), none) Hs Hs.length :=
    histOk_restart hrd hidx ⟨hv.1, hv.2.2.1⟩
  ihave #Hhc := walHistCertsK_alloc γn.cl sd Hs σ hrd $$ [Hc Hd]
  · iframe Hc Hd
  imod rnDurK_alloc_law_holds γn id x sd h σ Hs Hs.length ⟨S, σ.hs, none, l₀⟩ hv rfl hv.2.2.2.2.1 hok hrd
    $$ Hr Hc Hsy Hhc Hl HrS with ⟨%νk, %Hx, #Hinv, Hv, Hst, Hap, #Hlb, -⟩
  ihave #Hinv' := Hinv
  iunfold rnDurInvK at Hinv'
  icases Hinv' with ⟨%Hh, -⟩
  imodintro
  iexists νk
  iframe Hinv Hv Hst Hap Hlb
  ipureintro; exact ⟨Hx.1, Hx.2, Hh⟩

/-- `walSaveH.law` is the contract's `Save` (`walSaveHist_spec`, over the history). -/
theorem walSaveH_law_holds : walSaveH.law (GF := GF) :=
  fun st h ss si hst sized q hp hs sl esL cs Q => walSaveHist_spec st h ss si hst sized q hp hs sl esL cs Q

/-- `walSaveSnapH.law` is the contract's `SaveSnap` (`walSaveSnapHist_spec`). -/
theorem walSaveSnapH_law_holds : walSaveSnapH.law (GF := GF) :=
  fun st h ss si hst sized q sn mp dq m al Q => walSaveSnapHist_spec st h ss si hst q sn mp dq m al Q sized

end defs

end EtcdGrove
end Perennial
