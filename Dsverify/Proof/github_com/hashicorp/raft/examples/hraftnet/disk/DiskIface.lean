/-
(hraft_robust R3) `*Disk` as raft's log store (`isLogStore`, commit tracking: the right disjunct), its exact `FirstIndex` (`isLogStoreFirst`) and its stable store (`isStableStore`), from the methods' specs (hypotheses), the window families those of `diskInv`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__LastIndex
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__FirstIndex
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__GetLog
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__StoreLogs
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__StoreLog
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__DeleteRange
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__StageCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__GetCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__GetUint64
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__SetUint64
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__Get
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__Set

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

/-- **`*Disk` is a commit-tracking log store**, its view `diskOwnL g`, its window family `Wl`. -/
theorem disk_isLogStore
    (wp_LastIndex : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_GetLog : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.GetLog.spec (GF := GF) (hG := hG))
    (wp_StoreLogs : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.StoreLogs.spec (GF := GF) (hG := hG))
    (wp_StoreLog : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.StoreLog.spec (GF := GF) (hG := hG))
    (wp_DeleteRange : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.DeleteRange.spec (GF := GF) (hG := hG))
    (wp_StageCommitIndex : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.StageCommitIndex.spec (GF := GF) (hG := hG))
    (wp_GetCommitIndex : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.GetCommitIndex.spec (GF := GF) (hG := hG))
    (g : DiskGen) (d : Loc) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF) :
    isDisk (GF := GF) g d Wl Ws Wf ⊢
      isLogStore (interface.mk (go.GoType.PointerType Disk.ty) #d) (diskOwnL g) Wl := by
  iintro #Hd
  unfold isLogStore
  isplitr
  · imodintro
    iintro %tid %Φ Htok HAU
    iapply wp_wand_r
    isplitl [HAU]
    · iapply (wp_LastIndex g d Wl Ws Wf) $$ %(fun v => iprop(rtok tid -∗ Φ v)) Hd HAU
    iintro %v H; iapply H $$ Htok
  isplitr
  · imodintro
    iintro %tid %Φ Htok HΦ
    iapply wp_wand_r
    isplitl [HΦ]
    · iapply (wp_FirstIndex g d Wl Ws Wf) $$ %(fun v => iprop(rtok tid -∗ Φ v)) Hd
      iright; iexact HΦ
    iintro %v H; iapply H $$ Htok
  isplitr
  · imodintro
    iintro %idx %ptr %lv0 %tid %Φ Hptr Htok HAU
    iapply wp_wand_r
    isplitl [Hptr HAU]
    · iapply (wp_GetLog g d Wl Ws Wf idx ptr lv0) $$ %(fun v => iprop(rtok tid -∗ Φ v)) Hd Hptr HAU
    iintro %v H; iapply H $$ Htok
  isplitr
  · imodintro
    iintro %sl %dq %ptrs %first %es %Φ %Hlen Hsl Hptrs HW HAU
    iapply (wp_StoreLogs g d Wl Ws Wf sl dq ptrs first es) $$ %Φ [] Hd Hsl Hptrs HW HAU
    ipureintro; exact ⟨Hlen.1, Hlen.2.1, by omega⟩
  isplitr
  · imodintro
    iintro %p %first %e %Φ %Hf #Hp HW HAU
    iapply (wp_StoreLog g d Wl Ws Wf p first e) $$ %Φ [] Hd Hp HW HAU
    ipureintro; exact Hf
  isplitr
  · imodintro
    iintro %main %mn %mx %Φ %Hmx HW HAU
    iapply (wp_DeleteRange g d Wl Ws Wf main mn mx) $$ %Φ Hd HW HAU
  · iright
    isplitr
    · ipureintro; go_type_set
    isplitr
    · imodintro
      iintro %idx %Φ HAU
      iapply (wp_StageCommitIndex g d Wl Ws Wf idx) $$ %Φ Hd HAU
    · imodintro
      iintro %tid %Φ Htok HAU
      iapply wp_wand_r
      isplitl [HAU]
      · iapply (wp_GetCommitIndex g d Wl Ws Wf) $$ %(fun v => iprop(rtok tid -∗ Φ v)) Hd HAU
      iintro %v H; iapply H $$ Htok

/-- **`*Disk`'s `FirstIndex` is exact.** -/
theorem disk_isLogStoreFirst
    (wp_FirstIndex : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.FirstIndex.spec (GF := GF) (hG := hG))
    (g : DiskGen) (d : Loc) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF) :
    isDisk (GF := GF) g d Wl Ws Wf ⊢
      isLogStoreFirst (interface.mk (go.GoType.PointerType Disk.ty) #d) (diskOwnL g) := by
  iintro #Hd
  unfold isLogStoreFirst
  imodintro
  iintro %tid %Φ Htok HAU
  iapply wp_wand_r
  isplitl [HAU]
  · iapply (wp_FirstIndex g d Wl Ws Wf) $$ %(fun v => iprop(rtok tid -∗ Φ v)) Hd
    ileft; iexact HAU
  iintro %v H; iapply H $$ Htok

/-- **`*Disk` is a stable store**, its view `diskOwnS g`, its window family `Ws`. -/
theorem disk_isStableStore
    (wp_GetUint64 : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.GetUint64.spec (GF := GF) (hG := hG))
    (wp_SetUint64 : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.SetUint64.spec (GF := GF) (hG := hG))
    (wp_Get : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.Get.spec (GF := GF) (hG := hG))
    (wp_Set : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.Set.spec (GF := GF) (hG := hG))
    (g : DiskGen) (d : Loc) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF) :
    isDisk (GF := GF) g d Wl Ws Wf ⊢
      isStableStore (interface.mk (go.GoType.PointerType Disk.ty) #d) (diskOwnS g) Ws := by
  iintro #Hd
  unfold isStableStore
  isplitr
  · imodintro
    iintro %key %kb %tid %Φ #Hkey Htok HAU
    iapply wp_wand_r
    isplitl [HAU]
    · iapply (wp_GetUint64 g d Wl Ws Wf key kb) $$ %(fun v => iprop(rtok tid -∗ Φ v)) Hd Hkey HAU
    iintro %v H; iapply H $$ Htok
  isplitr
  · imodintro
    iintro %key %kb %v %Φ #Hkey HW HAU
    iapply (wp_SetUint64 g d Wl Ws Wf key kb v) $$ %Φ Hd Hkey HW HAU
  isplitr
  · imodintro
    iintro %key %kb %tid %Φ #Hkey Htok HAU
    iapply (wp_Get g d Wl Ws Wf key kb) $$ %Φ Hd Hkey [Htok HAU]
    iintro Hnc
    imod HAU $$ Hnc with ⟨Hnc, HAU⟩
    imodintro; iframe Hnc
    inext
    icases HAU with ⟨%st, Hown, Hcl⟩
    iexists st; iframe Hown
    iintro Hown
    imod Hcl $$ Hown with HΦ
    imodintro
    iapply HΦ $$ Htok
  · imodintro
    iintro %key %vs %kb %vb %Φ #Hkey #Hvs HW HAU
    iapply (wp_Set g d Wl Ws Wf key vs kb vb) $$ %Φ Hd Hkey Hvs HW HAU

end sec

end Perennial
