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

/-- **The loop's `Save`** (`rnDurK_save.law`). -/
theorem rnDurK_save_law_holds : rnDurK_save.law (GF := GF) := by
  intro γn id νk h v v' hs es γb nd st st' ms q Hst Hda Hidx Hcl
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
  obtain ⟨Hview, -, Hho⟩ := Hp
  obtain ⟨Hsok, Hview'⟩ := Hstep σ Hview
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists recsOf v σ, Hs
  iframe Hr
  isplitr
  · ipureintro; exact Hsok
  isplit
  · iintro ⟨Hr, -⟩
    imod Hmask with -
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
    · inext; ileft; iunfold rnDurBodyK
      iexists (v, none), σ, Hs, n
      iframe Hv0 Hcm Htn Hr Hsc Hsy Hhc Hlb Hraft
      ipureintro; exact ⟨Hview, fun _ _ _ hp => by simp at hp, Hho⟩
    imodintro
    iframe Hv Hok Hrec
  · iintro Hr
    icases walRecsH_fold h _ _ true $$ Hr with ⟨Hr, %Hf⟩
    imod Hmask with -
    let vk' : WalViewK := (v', some (v, γb, Hs.length))
    imod (ghostVar_update_halves vk' νk.ν.view (v, none) (v, none)) $$ Hv Hv0 with ⟨Hv, Hv0⟩
    imod (monoListAuthOwn_update (GF := GF) (γ := νk.ν.cm) v'.l Hpfx) $$ Hcm with ⟨Hcm, #Hcl'⟩
    have hr' : recsOf v' (walSave (recsOf v σ) hs es) = walSave (recsOf v σ) hs es := by
      unfold recsOf; rw [Hpn]
    have Hh' := Hview'.1
    have hb' : (walSave (recsOf v σ) hs es).b ≤ (walSave (recsOf v σ) hs es).commit := Hh'.2.2.2.2.2.1
    have hcl' := storageHolds_commit_le_last Hh' Hcl
    have Hho' : HistOkK vk' (Hs ++ [WalOpG.save hs es]) n :=
      histOk_save Hho Hf hb' hcl' ⟨Hh', Hview'.2.2.1⟩ Hidx
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft Hrec] with -
    · inext; ileft; iunfold rnDurBodyK
      ihave #Hhc' := walHistCerts_snoc γn.cl νk.sd Hs (WalOpG.save hs es) $$ [Hhc]
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
          obtain ⟨rfl, -, -⟩ := hp; exact Hda, Hho'⟩
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
    exact ⟨_, walRead_of_fold Hf hb'⟩

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
  obtain ⟨Hview, -, Hho⟩ := Hp
  obtain ⟨Hpre, Hview1⟩ := Hstep σ Hview
  have hr0 : recsOf v σ = σ := by unfold recsOf; rw [Hpn]
  icases walRecsH_fold h _ _ true $$ Hr with ⟨Hr, %Hf⟩
  rw [hr0] at Hf
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists recsOf v σ, Hs
  iframe Hr
  isplitr
  · ipureintro; rw [hr0]; exact Hpre
  isplit
  · iintro ⟨Hr, -⟩
    imod Hmask with -
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
    · inext; ileft; iunfold rnDurBodyK
      iexists (v, none), σ, Hs, n
      iframe Hv0 Hcm Htn Hr Hsc Hsy Hhc Hlb Hraft
      ipureintro; exact ⟨Hview, fun _ _ _ hp => by simp at hp, Hho⟩
    imodintro
    iframe Hv Hok
  · iintro Hr
    rw [hr0]
    icases walRecsH_saveSnap_baseLb h σ m _ true $$ Hr with ⟨Hr, #Hblb⟩
    imod Hmask with -
    let v2 : WalView := { v with pend := some m }
    imod (ghostVar_update_halves ((v2, none) : WalViewK) νk.ν.view (v, none) (v, none)) $$ Hv Hv0
      with ⟨Hv, Hv0⟩
    have hab : uint.nat (walLastHS Hs).Commit' < uint.nat m.Index' := by
      have h1 := Hview1.2.2.2.2.2 m rfl
      have h2 := walFoldChkFrom_fresh_hs Hf
      simp only [StorContents.commit] at h1
      rw [h2] at h1; exact h1
    have Hho' : HistOkK (v2, none) (Hs ++ [WalOpG.snap m al]) n :=
      histOk_snapAbove Hho Hf hab rfl rfl Hm61
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
    · inext; ileft; iunfold rnDurBodyK
      ihave #Hhc' := walHistCerts_snoc γn.cl νk.sd Hs (WalOpG.snap m al) $$ [Hhc]
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
      · ipureintro; exact ⟨Hview1, fun _ _ _ hp => by simp at hp, Hho'⟩
      have hd2 : durOf ((v2, none) : WalViewK) = durOf (v, none) := rfl
      have hp2 : rnPendK (GF := GF) γn id νk.x (v2, none) = rnPendK γn id νk.x (v, none) := rfl
      rw [hd2, hp2]
      iexact Hraft
    imodintro
    iunfold rnWalViewK
    iframe Hv Hok Hblb

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
  obtain ⟨Hview, Hpo, Hho⟩ := Hp
  iunfold walCommitLb at Hlbc
  ihave %Hpv := mono_list_auth_lb_valid νk.ν.cm 1 vk.1.l l $$ Hcm Hlbc
  obtain ⟨Hpre, σ', Hσ', Hok1⟩ := walOwnSnapStep vk.1 σ md l e Hpv.2 Hpos He Ht Hview
  icases walRecsH_fold h _ _ true $$ Hr with ⟨Hr, %Hf⟩
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  iexists recsOf vk.1 σ, Hs
  iframe Hr
  isplitr
  · ipureintro; exact Hpre
  isplit
  · iintro ⟨Hr, -⟩
    imod Hmask with -
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
    · inext; ileft; iunfold rnDurBodyK
      iexists vk, σ, Hs, n
      iframe Hv0 Hcm Htn Hr Hsc Hsy Hhc Hlb Hraft
      ipureintro; exact ⟨Hview, Hpo, Hho⟩
    imodintro
    iframe Ha
  · iintro Hr
    icases walRecsH_saveSnap_baseLb h _ md _ true $$ Hr with ⟨Hr, #Hblb⟩
    imod Hmask with -
    have hil : uint.nat md.Index' - 1 < l.length := (List.getElem?_eq_some_iff.1 He).1
    have He' : vk.1.l[uint.nat md.Index' - 1]? = some e := by
      obtain ⟨t, ht⟩ := Hpv.2
      rw [← ht, List.getElem?_append_left hil]; exact He
    have hlen : l.length ≤ vk.1.l.length := Hpv.2.length_le
    have hc : uint.nat md.Index' ≤ uint.nat (walLastHS Hs).Commit' := by
      have h2 := walFoldChkFrom_fresh_hs Hf
      have h3 : (recsOf vk.1 σ).hs = σ.hs := by
        unfold recsOf; split
        · rfl
        · exact walSaveSnap_hs _ _
      rw [← h2, h3]
      have := Hview.2.2.2.1
      simp only [StorContents.commit] at this
      omega
    have Hho' : HistOkK vk (Hs ++ [WalOpG.snap md al]) n :=
      histOk_ownSnap Hho Hf hc Hview.2.2.2.2.1 Hpos He' Ht Hm61
    imod Hclose $$ [Hv0 Hcm Htn Hr Hraft] with -
    · inext; ileft; iunfold rnDurBodyK
      ihave #Hhc' := walHistCerts_snoc γn.cl νk.sd Hs (WalOpG.snap md al) $$ [Hhc]
      · iframe Hhc; simp only [walOpCert]; iframe Hsv Hsd
      ihave #Hsc' := walSnapCert_saveSnap γn.cl _ md $$ [Hsc]
      · iframe Hsc Hsv
      iexists vk, σ', Hs ++ [WalOpG.snap md al], n
      rw [Hσ']
      iframe Hv0 Hcm Htn Hr Hsc' Hsy Hhc' Hlb Hraft
      ipureintro; exact ⟨Hok1, Hpo, Hho'⟩
    imodintro
    iframe Ha Hblb

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
  obtain ⟨Hview, -, Hho⟩ := Hp
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
  · have Hho' : HistOkK (v', none) Hs (max n (pos + 1)) := histOk_enter Hho (Or.inl rfl)
    imod Hclose $$ [Hv0 Hcm Htn Hr HrS] with -
    · inext; ileft; iunfold rnDurBodyK
      iexists (v', none), σ, Hs, max n (pos + 1)
      iframe Hv0 Hcm Htn Hr Hsc Hhc
      isplitr
      · rcases Nat.le_total n (pos + 1) with hle | hle
        · rw [Nat.max_eq_right hle]; iexact Hsy'
        · rw [Nat.max_eq_left hle]; iexact Hsy
      isplitr
      · iunfold rnLogLbsK; iunfold rnLogLbsK at Hlb
        icases Hlb with ⟨#Hl, -⟩
        iframe Hl
      isplitr
      · ipureintro; exact ⟨Hview, fun _ _ _ hp => by simp at hp, Hho'⟩
      ileft; simp only [durOf]; iframe HrS
      rw [rnPendK_none]; itrivial
    imodintro
    iframe Hnc Hdrv Hmsgs Hrun
    iunfold rnWalViewK
    iframe Hv Hok
  · have Hho' : HistOkK (v', none) Hs n := histOk_enter Hho (Or.inr ⟨rfl, Himp⟩)
    imod Hclose $$ [Hv0 Hcm Htn Hr HrS] with -
    · inext; ileft; iunfold rnDurBodyK
      iexists (v', none), σ, Hs, n
      iframe Hv0 Hcm Htn Hr Hsc Hhc Hsy
      isplitr
      · iunfold rnLogLbsK; iunfold rnLogLbsK at Hlb
        icases Hlb with ⟨#Hl, -⟩
        iframe Hl
      isplitr
      · ipureintro; exact ⟨Hview, fun _ _ _ hp => by simp at hp, Hho'⟩
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
  obtain ⟨Hview, -, -⟩ := Hp
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
  · iapply walRecsH_walRecs; iexact Hr
  ipureintro
  obtain ⟨Hh, Hhs, Hb, Hc, Hag, -⟩ := Hview
  exact ⟨Hh, Hb, Hc, Hhs, Hag⟩

/-- **The allocation** (`rnDurK_alloc.law`). -/
theorem rnDurK_alloc_law_holds : rnDurK_alloc.law (GF := GF) := by
  intro γn id x sd h σ Hs n v Hv Hpn Hda Hho
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
    · ipureintro; exact ⟨Hv, fun _ _ _ hp => by simp at hp, Hho⟩
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

/-- `walSaveH.law` is the contract's `Save` (`walSaveSized_spec`, over the records with their history). -/
theorem walSaveH_law_holds : walSaveH.law (GF := GF) :=
  fun st h ss si hst sized q hp hs sl esL cs Q => walSaveSized_spec st h ss si hst sized q hp hs sl esL cs Q

/-- `walSaveSnapH.law` is the contract's `SaveSnap` (`walSaveSnapH_spec`). -/
theorem walSaveSnapH_law_holds : walSaveSnapH.law (GF := GF) :=
  fun st h ss si hst sized q sn mp dq m al Q => walSaveSnapH_spec st h ss si hst q sn mp dq m al Q sized

end defs

end EtcdGrove
end Perennial
