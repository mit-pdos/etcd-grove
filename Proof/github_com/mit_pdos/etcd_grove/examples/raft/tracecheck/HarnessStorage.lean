/-
Lean-first (no Rocq counterpart). Trace-check's layer D (the harness, 2026-11-12;
`notes/trace-check-design.md` §2.2, the storage row): **each replica's `MemoryStorage` at raft's node
API**. The harness hands raft a `*MemoryStorage` itself (no wrapper), registered in raft's registry
(`MemStorReg`, `memStorageModel`), which the harness allocates.

* `tcJ γ K`: the storage's justifications, as raft's `memStorJ` but **never compacting**: a
  compaction right only at `0` (`B k := ⌜k = 0⌝`; the harness never calls `Compact`,
  `SnapshotEvery = 0`). The contract's compaction bound is then `storBnd γ K 0` only
  (`tc_storBnd_zero`; the design's `storBnd_zero`, B2).
* `tc_isStorage`: a registered storage with its invariant at `tcJ γ K` meets the storage contract of
  key `K` (`memStorage_isStorageP`, its bound weakened to `storBnd`: `isStorageP_bnd`).
* `tc_bootStorage`: `StartNode`'s `restartStorage` premise at the empty contents, from what
  `NewMemoryStorage` gives, as kvreconf's `kvr_bootStorage` for a raw `MemoryStorage`: its
  `InitialState` (the storage's own, detached: `memStorFresh`) gives the bootstrap conf state, and at
  the key raft names the storage by, the invariant is allocated (`memStorInvP_alloc`).
* `memStorMeta_excl`: a storage's metadata is held once (so a storage is registered once).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Defs
public import Proof.go_etcd_io.raft.v3.MemstorageInstance
public import Spec.go_etcd_io.raft.v3.MemoryStorage__InitialState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__LastIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Term
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Entries
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section storage
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [MemStorReg GF]

attribute [local instance] memStorageModel

/-- The harness's storage justifications (see the file header): raft's `memStorJ`, compacting at
`0` only. -/
def tcJ (γ : Cluster) (K : GName) : MemJust GF where
  SV := snapshotValid γ
  B k := iprop(⌜k = 0⌝)
  DL := nodeCommitLb γ K
  SV_pers := fun sv => by infer_instance
  B_pers := fun k => by infer_instance
  B_timeless := fun k => by infer_instance
  DL_pers := fun i => by infer_instance

/-- **No compaction past `0`** (the design's `storBnd_zero`, B2): the node API's storage bound at
`0`, from raft's applied bound at `0`. -/
theorem tc_storBnd_zero (γ : Cluster) (K : GName) : ⊢ storBnd (GF := GF) γ K 0 := by
  unfold storBnd
  iintro
  iexists 0
  isplitr
  · ipureintro; exact Nat.le_refl 0
  iapply nodeAppliedLb_zero γ K

/-- The storage contract with a weaker compaction bound. -/
theorem isStorageP_bnd (SV : SnapshotM → IProp GF) (B1 B2 : Nat → IProp GF) (DL : Nat → IProp GF)
    (st : Storage) :
    ⊢ isStorageP SV B1 DL st -∗ □ (∀ c, B1 c ={⊤}=∗ B2 c) -∗ isStorageP SV B2 DL st := by
  iintro #H #Hb
  unfold isStorageP
  icases H with ⟨%i, %Hst, #H1, #H2, #H3, #H4, #H5, #Hbound, #Hlen⟩
  iexists i
  iframe H1 H2 H3 H4 H5 Hlen
  isplitr
  · ipureintro; exact Hst
  iintro !> %c #Hc
  imod Hbound $$ %c Hc with HB
  iapply Hb $$ %c HB

/-- **A registered `MemoryStorage` with its invariant at `tcJ γ K` meets the storage contract of
key `K`.** -/
theorem tc_isStorage
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName) :
    ⊢ memStorInvP (GF := GF) ms γs (tcJ γ K) -∗ memStorReg ms γs -∗
      isStorage γ K (memStorIface ms) := by
  iintro #Hinv #Hreg
  ihave #H := memStorage_isStorageP wp_LastIndex wp_FirstIndex wp_Term wp_Entries wp_Snapshot ms γs
    (tcJ γ K) $$ Hinv Hreg
  ihave #H' : isStorageP (snapshotValid γ) (memBnd (tcJ γ K)) (nodeCommitLb γ K) (memStorIface ms)
    $$ []
  · iExactEq H; rfl
  unfold isStorage
  iapply isStorageP_bnd (snapshotValid γ) (memBnd (tcJ γ K)) (storBnd γ K) (nodeCommitLb γ K)
    (memStorIface ms) $$ H'
  iintro !> %c #Hc
  unfold memBnd tcJ
  icases Hc with ⟨%k, %Hck, %Hk⟩
  subst Hk
  have : c = 0 := by omega
  subst this
  imodintro
  iapply tc_storBnd_zero γ K

/-- The empty contents a fresh storage starts a node from. -/
abbrev tcBootContents : StorContents :=
  ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩

/-- **A fresh `MemoryStorage` before `StartNode`** (see the file header): its `FirstIndex` is `1`, its
`LastIndex` `0`, and its `InitialState` gives the empty hard state, the bootstrap conf state, and at
the key `K` raft names the storage by the contract, the storage's (empty) log and the frame `F K`,
built from the storage's metadata and invariant (`HF`). -/
theorem tc_bootStorage
    (wp_InitialState : MemoryStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (ms : Loc) (γs : MemStorNames) (γ : Cluster) (F : GName → IProp GF) :
    ⊢ memStorReg (GF := GF) ms γs -∗ memStorLock ms γs -∗ memStorFresh ms γs 0 memSnapEmpty -∗
      memStorMeta ms γs tcBootContents.hs -∗
      memLog γs 0 DFrac.discard [zero_val EntryM] -∗ memEnd γs 1 -∗
      (∀ K : GName, memStorMeta ms γs tcBootContents.hs -∗ memStorInvP ms γs (tcJ γ K) -∗ F K) -∗
      restartStorage γ (memStorIface ms) tcBootContents memSnapEmpty.Metadata'.ConfState' 0 F := by
  iintro #Hreg #Hl Hfresh Hmeta #Hlog He HF
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  unfold restartStorage
  iexists (interface.mk (go.GoType.PointerType MemoryStorage.ty) #ms)
  iexists iprop(memStorFresh ms γs 0 memSnapEmpty ∗ memStorMeta ms γs tcBootContents.hs ∗
    memEnd γs 1 ∗
    (∀ K : GName, memStorMeta ms γs tcBootContents.hs -∗ memStorInvP ms γs (tcJ γ K) -∗ F K))
  iexists 0
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; simp [StorContents.b, StorContents.commit]
  isplitl [Hfresh Hmeta He HF]
  · iframe Hfresh Hmeta He HF
  isplitr
  · iintro !> %Φ ⟨Hfresh, Hmeta, He, HF⟩ HΦ
    wp_apply wp_FirstIndex ms γs 0 $$ [$Hinit $Hl] as %fi ⟨%Hfi, #Hc⟩
    · iapply memCompacted_zero
    icases memStorFresh_compacted ms γs _ _ _ $$ [$Hfresh $Hc] with ⟨%H0, Hfresh⟩
    have Hfi1 : fi = W64 (StorContents.b tcBootContents + 1) := by
      simp only [StorContents.b]; word
    rw [Hfi1]
    iapply HΦ
    iframe Hfresh Hmeta He HF
  isplitr
  · iintro !> %Φ ⟨Hfresh, Hmeta, He, HF⟩ HΦ
    wp_apply wp_LastIndex ms γs 1 $$ [$Hinit $Hl $He] as %li ⟨He, %Hli⟩
    have Hli0 : li = W64 (StorContents.last tcBootContents) := by
      simp only [StorContents.last, StorContents.b, List.length_nil]; word
    rw [Hli0]
    iapply HΦ
    iframe Hfresh Hmeta He HF
  iintro !> %Φ ⟨Hfresh, Hmeta, He, HF⟩ HΦ
  iapply wp_fupd
  wp_apply wp_InitialState ms γs tcBootContents.hs 0 memSnapEmpty $$ [$Hinit $Hmeta $Hfresh]
    as %hp %cs ⟨#Hhs, Hmeta, Hfresh, #Hcs⟩
  imodintro
  iapply HΦ $$ %hp %cs %true
  isplitr
  · iexact Hhs
  isplitr
  · iExactEq Hcs; rfl
  iintro %K #HA #HD
  imod memStorInvP_alloc ms γs (tcJ γ K) ⊤ 0 memSnapEmpty $$ Hl Hfresh [] [] with #Hinv
  · iintro !> %k %hk
    unfold tcJ
    ipureintro; omega
  · ileft; ipureintro; rfl
  ihave HFK := HF $$ %K Hmeta Hinv
  imodintro
  isplitr
  · iapply tc_isStorage wp_LastIndex wp_FirstIndex wp_Term wp_Entries wp_Snapshot ms γs γ K
      $$ Hinv Hreg
  iframe HFK
  iunfold storHolds
  have hb : tcBootContents.b = 0 := by simp [StorContents.b]
  have hl : tcBootContents.last = 0 := by simp [StorContents.last, StorContents.b]
  rw [hl, hb, Nat.zero_add]
  simp only [Nat.sub_self, List.take_zero, List.drop_zero]
  iexists (zero_val EntryM)
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply memStorCompacted_of ms γs 0 $$ Hreg
    iapply memCompacted_zero
  isplitr
  · iapply memStorLog_of ms γs 0 DFrac.discard [zero_val EntryM] $$ Hreg Hlog
  isplitr
  · iapply memStorLog_of ms γs 1 DFrac.discard [] $$ Hreg
    iapply memLog_nil
  isplitr
  · iapply memStorLog_of ms γs 1 (DFrac.own 1) [] $$ Hreg
    iapply memLog_nil
  iapply memStorEnd_of ms γs 1 $$ Hreg He

/-- **A storage's metadata is held once.** -/
theorem memStorMeta_excl (ms : Loc) (γs1 γs2 : MemStorNames) (hs1 hs2 : HardStateM) :
    ⊢ memStorMeta (GF := GF) ms γs1 hs1 -∗ memStorMeta ms γs2 hs2 -∗ False := by
  iintro H1 H2
  iunfold memStorMeta at H1 H2
  icases H1 with ⟨%n1, %hp1, -, -, -, -, H1⟩
  icases H2 with ⟨%n2, %hp2, -, -, -, -, H2⟩
  ihave H1 := typedPointsto_split _ _ _ $$ H1
  ihave H2 := typedPointsto_split _ _ _ $$ H2
  rw [typedPointstoDef_w64, typedPointstoDef_w64]
  obtain ⟨b1, bs1, hb1⟩ : ∃ b bs, natBytes 8 n1.toNat = b :: bs := by
    cases h : natBytes 8 n1.toNat with
    | nil => have := natBytes_length 8 n1.toNat; rw [h] at this; simp at this
    | cons b bs => exact ⟨b, bs, rfl⟩
  obtain ⟨b2, bs2, hb2⟩ : ∃ b bs, natBytes 8 n2.toNat = b :: bs := by
    cases h : natBytes 8 n2.toNat with
    | nil => have := natBytes_length 8 n2.toNat; rw [h] at this; simp at this
    | cons b bs => exact ⟨b, bs, rfl⟩
  rw [hb1, hb2]
  simp only [bytesPointsto]
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  icombine H1 H2 gives %H
  exfalso
  have := DFrac.valid_own_op H.1
  have h1 : (1 : Qp).val = 1 := rfl
  grind

end storage

end TraceCheck
end EtcdGrove
end Perennial
