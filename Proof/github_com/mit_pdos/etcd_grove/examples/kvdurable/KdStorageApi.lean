/-
Lean-first (no Rocq counterpart).

# The store's storage at raft's node API (2026-11-01, stage II (j), S4)

kvreconf's `KvrStorageApi.lean` at kvdurable's wrapper (`KdStorage.lean`'s vocabulary):

- **the promoted read methods** raft's storage contract calls (`Storage.wp_FirstIndex`,
  `wp_LastIndex`, `wp_Term`, `wp_Entries`): the `MemoryStorage`'s specs at the wrapper (the method
  resolved on `*Storage` loads the embedded `MemoryStorage`). kvdurable's own wrappers of the
  storage's changes (`Storage.{Append, ApplySnapshot, SetHardState, CreateSnapshot, Compact}`) have
  their own specs and proofs.
- **the contract** (`kdStorage_isStorage`): a registered wrapper whose `MemoryStorage` has its
  invariant at `kdJ γ K` is the storage of key `K`. kvdurable's `Storage` overrides `Snapshot` (the
  attached spec, `Storage.Snapshot.spec`, kvreconf's) and `InitialState`, which only raft's start
  calls, in the detached mode (`Storage.InitialState.spec`): it is used only in `kd_restartStorage`.
- **the start premise** (`kd_restartStorage`): `RestartNode`'s `restartStorage` of a storage holding
  the contents of a file `f` (`kdContents (some f)`; `imgEmpty` for no file), from what `openStorage`
  (or `newStorage`) gives, detached: the frame `R` holds the detached token, the hard state's
  metadata and the log; `InitialState`'s continuation, at the key `K` raft names the storage by,
  allocates the storage's invariant `memStorInvP ms γs (kdJ γ K)` (`memStorInvP_alloc`, from raft's
  bounds at the attach and the stored snapshot's validity), builds the contract and gives the log,
  and the client's frame `F K` from the metadata and the invariant.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__InitialState
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage__Snapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__LastIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Term
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Entries

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section promoted
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [KdStor GF]

theorem Storage.wp_FirstIndex (wp : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (c : Nat) :
  {{ kdStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memCompacted γs c) }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"FirstIndex")) (Val #()))
  {{ (fi : w64), RET (PairV #fi #interface.nil);
      ⌜c + 1 ≤ uint.nat fi⌝ ∗ memCompacted γs (uint.nat fi - 1) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kdStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs c $$ [HP] as %fi HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem Storage.wp_LastIndex (wp : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (e : Nat) :
  {{ kdStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗ memEnd γs e) }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"LastIndex")) (Val #()))
  {{ (li : w64), RET (PairV #li #interface.nil); memEnd γs e ∗ ⌜uint.nat li + 1 = e⌝ }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kdStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs e $$ [HP] as %li HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem Storage.wp_Term (wp : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) (i0 : w64)
    (ec : GoInterface) :
  {{ kdStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memLog γs k dq es ∗ ⌜k ≤ uint.nat i0 ∧ uint.nat i0 < k + es.length⌝ ∗
      globalAddr ErrCompacted ↦□ ec) }}
    (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"Term")) (Val #i0))
  {{ (t : w64) (err : GoInterface), RET (PairV #t #err);
      memLog γs k dq es ∗
      (⌜err = interface.nil ∧ (fun e : EntryM => e.Term') <$> es[uint.nat i0 - k]? = some t⌝ ∨
       (⌜err = ec⌝ ∗ memCompacted γs (uint.nat i0 + 1))) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kdStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs k dq es i0 ec $$ [HP] as %t %err HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem Storage.wp_Entries (wp : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq1 dq2 : DFrac) (a b : List EntryM)
    (lo hi maxSize : w64) (ec : GoInterface) :
  {{ kdStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memLog γs k dq1 a ∗ memLog γs (k + a.length) dq2 b ∗
      ⌜k ≤ uint.nat lo ∧ uint.nat lo < uint.nat hi ∧ uint.nat hi ≤ k + a.length + b.length⌝ ∗
      globalAddr ErrCompacted ↦□ ec) }}
    (App (App (App (Val (s @!! go.GoType.PointerType kStorageTy @!! go!"Entries")) (Val #lo))
      (Val #hi)) (Val #maxSize))
  {{ (sl : GoSlice) (es : List EntryM) (err : GoInterface), RET (PairV #sl #err);
      memLog γs k dq1 a ∗ memLog γs (k + a.length) dq2 b ∗
      ((⌜err = ec⌝ ∗ memCompacted γs (uint.nat lo)) ∨
       (⌜err = interface.nil⌝ ∗ entsRO sl es ∗
        ⌜es ≠ [] ∧ sl.cap = sl.len ∧
          es <+: ((a ++ b).drop (uint.nat lo - k)).take (uint.nat hi - uint.nat lo)⌝)) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kdStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs k dq1 dq2 a b lo hi maxSize ec $$ [HP] as %sl %es %err HQ
  · iexact HP
  iapply HΦ
  iexact HQ

end promoted

section api
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]
attribute [local instance] kdStorageModel

/-- `kdJ`'s compaction justification is the API's (`storBnd`). -/
theorem kdJ_bnd (γ : Cluster) (K : GName) (c : Nat) :
    memBnd (kdJ (GF := GF) γ K) c ⊢ storBnd γ K c := by
  unfold memBnd storBnd kdJ; exact .rfl

/-- **The store's storage meets the storage contract of key `K`** (under `kdStorageModel`;
kvreconf's `kvrStorage_isStorage`). -/
theorem kdStorage_isStorage
    (wp_Snapshot : Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable -∗
      kdStorRec s ms γs -∗ memStorInvP ms γs (kdJ γ K) -∗
      isStorage γ K (kdStorIface s) := by
  iintro #Hpkg #Hrec #Hinv
  ihave #Hl : memStorLock ms γs $$ []
  · iunfold memStorInvP at Hinv; icases Hinv with ⟨#Hl, -⟩; iexact Hl
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  unfold isStorage isStorageP
  iexists (interface.mk (go.GoType.PointerType kStorageTy) #s)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %e
    imodintro
    iintro %Φ He HΦ
    ihave He := kdStorEnd_to s ms γs e $$ Hrec He
    wp_apply Storage.wp_LastIndex wp_LastIndex s ms γs e $$ [$Hrec $Hinit $Hl $He] as %li ⟨He, %Hli⟩
    iapply HΦ
    ihave He := kdStorEnd_of s ms γs e $$ Hrec He
    iframe He
    ipureintro; exact Hli
  isplitr
  · iintro %k %dq %es %i0 %ec
    imodintro
    iintro %Φ ⟨H, %Hr, #Hec⟩ HΦ
    ihave H := kdStorLog_to s ms γs k dq es $$ Hrec H
    wp_apply Storage.wp_Term wp_Term s ms γs k dq es i0 ec $$ [$Hrec $Hinit $Hl $H $Hec]
      as %t %err ⟨H, Ht⟩
    · ipureintro; exact Hr
    iapply HΦ
    ihave H := kdStorLog_of s ms γs k dq es $$ Hrec H
    iframe H
    icases Ht with (%Ht | ⟨%Ht, #Hc⟩)
    · ileft; ipureintro; exact Ht
    · iright
      isplitr
      · ipureintro; exact Ht
      iapply kdStorCompacted_of s ms γs _ $$ Hrec Hc
  isplitr
  · iintro %k %dq1 %dq2 %a %b %lo %hi %maxSize %ec
    imodintro
    iintro %Φ ⟨Ha, Hb, %Hr, #Hec⟩ HΦ
    ihave Ha := kdStorLog_to s ms γs k dq1 a $$ Hrec Ha
    ihave Hb := kdStorLog_to s ms γs (k + a.length) dq2 b $$ Hrec Hb
    wp_apply Storage.wp_Entries wp_Entries s ms γs k dq1 dq2 a b lo hi maxSize ec
      $$ [$Hrec $Hinit $Hl $Ha $Hb $Hec] as %sl %es %err ⟨Ha, Hb, Hres⟩
    · ipureintro; exact Hr
    iapply HΦ $$ %sl %es %err
    ihave Ha := kdStorLog_of s ms γs k dq1 a $$ Hrec Ha
    ihave Hb := kdStorLog_of s ms γs (k + a.length) dq2 b $$ Hrec Hb
    iframe Ha Hb
    icases Hres with (⟨%He, #Hc⟩ | Hres)
    · ileft
      isplitr
      · ipureintro; exact He
      iapply kdStorCompacted_of s ms γs _ $$ Hrec Hc
    · iright; iexact Hres
  isplitr
  · iintro %c
    imodintro
    iintro %Φ #Hc HΦ
    ihave #Hc := kdStorCompacted_to s ms γs c $$ Hrec Hc
    wp_apply Storage.wp_FirstIndex wp_FirstIndex s ms γs c $$ [$Hrec $Hinit $Hl $Hc]
      as %fi ⟨%Hfi, #Hc'⟩
    iapply HΦ
    isplitr
    · ipureintro; exact Hfi
    iapply kdStorCompacted_of s ms γs _ $$ Hrec Hc'
  isplitr
  · iintro %c %esu
    imodintro
    iintro %Φ ⟨#Hc, #Hesu⟩ HΦ
    ihave #Hc := kdStorCompacted_to s ms γs c $$ Hrec Hc
    wp_apply wp_Snapshot s ms γs (kdJ γ K) c esu $$ [$Hpkg $Hrec $Hinv $Hc $Hesu]
      as %snap %err Hres
    iapply HΦ
    iexact Hres
  isplitr
  · iintro !> %c #Hc
    ihave #Hc := kdStorCompacted_to s ms γs c $$ Hrec Hc
    imod memCompacted_bound ms γs (kdJ γ K) c $$ Hinv Hc with Hb
    imodintro
    iapply kdJ_bnd γ K c $$ Hb
  iintro !> %k %dq %es H
  ihave H := kdStorLog_to s ms γs k dq es $$ Hrec H
  iunfold memLog at H
  icases H with ⟨H, %Hb⟩
  isplitr
  · ipureintro; exact Hb
  iapply kdStorLog_of s ms γs k dq es $$ Hrec
  iunfold memLog
  iframe H
  ipureintro; exact Hb

/-- The stored snapshot `openStorage` gives `memStorFresh` at: the file's, or the empty one at
index `0`. -/
def kdFreshSnap (f : StorFile) : SnapshotM :=
  if f.snap.Metadata'.Index' = W64 0 then memSnapEmpty else f.snap

/-- The conf state a storage of the file `f` (of bootstrap conf state `boot`) reports
(`Storage.InitialState`): the stored snapshot's, or the bootstrap one at index `0`. -/
def kdInitCS (boot : ConfStateM) (f : StorFile) : ConfStateM :=
  if f.snap.Metadata'.Index' = W64 0 then boot else f.snap.Metadata'.ConfState'

theorem kdFreshSnap_index_zero (f : StorFile) :
    (kdFreshSnap f).Metadata'.Index' = W64 0 ↔ f.snap.Metadata'.Index' = W64 0 := by
  unfold kdFreshSnap
  by_cases h : f.snap.Metadata'.Index' = W64 0
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]

theorem kdInitCS_fresh (boot : ConfStateM) (f : StorFile) :
    (if (kdFreshSnap f).Metadata'.Index' = W64 0 then boot else (kdFreshSnap f).Metadata'.ConfState')
      = kdInitCS boot f := by
  unfold kdInitCS kdFreshSnap
  by_cases h : f.snap.Metadata'.Index' = W64 0
  · rw [if_pos h, if_pos h]; exact if_pos rfl
  · rw [if_neg h, if_neg h]

theorem kdContents_some_hs (f : StorFile) : (kdContents (some f)).hs = f.hs := rfl
theorem kdContents_some_b (f : StorFile) : (kdContents (some f)).b = uint.nat f.prev := rfl
theorem kdContents_some_ents (f : StorFile) : (kdContents (some f)).ents = f.ents := rfl
theorem kdContents_some_last (f : StorFile) :
    (kdContents (some f)).last = uint.nat f.prev + f.ents.length := rfl
theorem kdContents_some_commit (f : StorFile) :
    (kdContents (some f)).commit = uint.nat f.hs.Commit' := rfl
theorem kdContents_some_base_term (f : StorFile) :
    (kdContents (some f)).base.term' = f.prevTerm := rfl

/-- **A storage of the file `f` before `RestartNode`** (`RestartNode`'s `restartStorage` premise at
`kdContents (some f)`, raft's applied index `A`; see the file header): from what `openStorage` (or
`newStorage`, at `imgEmpty`) gives of the storage, detached, and the stored snapshot's validity
(its certificate's). The frame `F` is the client's, from the hard state's metadata and the
invariant at the key (`HF`). -/
theorem kd_restartStorage
    (wp_InitialState : Storage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (s ms bp : Loc) (γs : MemStorNames) (f : StorFile) (boot : ConfStateM) (e0 : EntryM)
    (γ : Cluster) (A : Nat) (F : GName → IProp GF)
    (Hok : KdFileOk f) (He0 : e0.Term' = f.prevTerm)
    (Hsc : uint.nat f.snap.Metadata'.Index' ≤ uint.nat f.hs.Commit') :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable -∗
      kdStorRec s ms γs -∗ kdStorBoot s bp boot -∗
      memStorLock ms γs -∗ memStorFresh ms γs (uint.nat f.prev) (kdFreshSnap f) -∗
      memStorMeta ms γs f.hs -∗
      memLog γs (uint.nat f.prev) DFrac.discard [e0] -∗
      memLog γs (uint.nat f.prev + 1) (DFrac.own 1) f.ents -∗
      memEnd γs (uint.nat f.prev + f.ents.length + 1) -∗
      memCompacted γs (uint.nat f.prev) -∗
      (⌜f.snap.Metadata'.Index' = W64 0⌝ ∨ snapshotValid γ f.snap) -∗
      (∀ K : GName, memStorMeta ms γs f.hs -∗ memStorInvP ms γs (kdJ γ K) -∗ F K) -∗
      restartStorage γ (kdStorIface s) (kdContents (some f)) (kdInitCS boot f) A F := by
  iintro #Hpkg #Hrec #Hboot #Hl Hfresh Hmeta #He0 Hents Hend #Hc Hval HF
  obtain ⟨-, Hp61, Hlen, -, -, -, -, -⟩ := Hok
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  ihave #Hrec' := Hrec
  iunfold kdStorRec at Hrec'
  icases Hrec' with ⟨#Hf, -⟩
  unfold restartStorage storHolds
  simp only [kdContents_some_hs, kdContents_some_b, kdContents_some_ents, kdContents_some_last,
    kdContents_some_commit, kdContents_some_base_term]
  iexists (interface.mk (go.GoType.PointerType kStorageTy) #s)
  iexists iprop(memStorFresh ms γs (uint.nat f.prev) (kdFreshSnap f) ∗ memStorMeta ms γs f.hs ∗
    memLog γs (uint.nat f.prev + 1) (DFrac.own 1) f.ents ∗
    memEnd γs (uint.nat f.prev + f.ents.length + 1) ∗
    (⌜f.snap.Metadata'.Index' = W64 0⌝ ∨ snapshotValid γ f.snap) ∗
    (∀ K : GName, memStorMeta ms γs f.hs -∗ memStorInvP ms γs (kdJ γ K) -∗ F K))
  isplitr
  · ipureintro; rfl
  isplitl [Hfresh Hmeta Hents Hend Hval HF]
  · iframe
  isplitr
  · -- FirstIndex: the log's start plus one (detached: compacted at most at the start)
    iintro !> %Φ ⟨Hfresh, HR⟩ HΦ
    wp_apply Storage.wp_FirstIndex wp_FirstIndex s ms γs (uint.nat f.prev)
      $$ [$Hrec $Hraft $Hl $Hc] as %fi ⟨%Hfi, #Hc'⟩
    ihave ⟨%Hle, Hfresh⟩ := memStorFresh_compacted ms γs _ _ _ $$ [$Hfresh $Hc']
    have Hfi' : fi = W64 (uint.nat f.prev + 1) := by word
    subst Hfi'
    iapply HΦ
    iframe
  isplitr
  · -- LastIndex: the log's last index
    iintro !> %Φ ⟨Hfresh, Hmeta, Hents, Hend, HR⟩ HΦ
    wp_apply Storage.wp_LastIndex wp_LastIndex s ms γs _ $$ [$Hrec $Hraft $Hl $Hend]
      as %li ⟨Hend, %Hli⟩
    have Hli' : li = W64 (((uint.nat f.prev + f.ents.length : Nat)) : Int) := by word
    subst Hli'
    iapply HΦ
    iframe
  -- InitialState: detached; its continuation attaches the storage at raft's key
  iintro !> %Φ ⟨Hfresh, Hmeta, Hents, Hend, Hval, HF⟩ HΦ
  wp_apply wp_InitialState s ms bp γs f.hs (uint.nat f.prev) (kdFreshSnap f) boot
    $$ [$Hpkg $Hrec $Hboot $Hl $Hmeta $Hfresh] as %hp %cs %al ⟨Hhs, -, Hmeta, Hfresh, Hcs⟩
  iapply HΦ
  isplitl [Hhs]
  · iexact Hhs
  isplitl [Hcs]
  · iExactEq Hcs; rw [kdInitCS_fresh]
  iintro %K #HAl #HCl
  ihave #HB : □ (∀ k, ⌜k ≤ uint.nat f.prev⌝ -∗ (kdJ γ K).B k) $$ []
  · iintro !> %k %hk
    simp only [kdJ]
    iapply nodeAppliedLb_mono γ K _ k (by omega) $$ HAl
  ihave Hsv : (⌜(kdFreshSnap f).Metadata'.Index' = W64 0⌝ ∨
      (kdJ γ K).SV (kdFreshSnap f) ∗ (kdJ γ K).DL (uint.nat (kdFreshSnap f).Metadata'.Index'))
    $$ [Hval]
  · by_cases h0 : f.snap.Metadata'.Index' = W64 0
    · ileft; ipureintro; exact (kdFreshSnap_index_zero f).2 h0
    · have hfs : kdFreshSnap f = f.snap := by unfold kdFreshSnap; rw [if_neg h0]
      rw [hfs]
      icases Hval with (%H | #Hv)
      · exact absurd H h0
      iright
      simp only [kdJ]
      isplitr
      · iexact Hv
      iapply nodeCommitLb_mono γ K _ _ (by omega) $$ HCl
  imod memStorInvP_alloc ms γs (kdJ γ K) ⊤ (uint.nat f.prev) (kdFreshSnap f) $$ Hl Hfresh HB Hsv
    with #Hinv
  ihave #Hst := kdStorage_isStorage wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term wp_Entries
    s ms γs γ K $$ Hpkg Hrec Hinv
  ihave HFK := HF $$ %K Hmeta Hinv
  imodintro
  iframe Hst HFK
  iexists e0
  isplitr
  · ipureintro; exact He0
  isplitr
  · iapply kdStorCompacted_of s ms γs _ $$ Hrec Hc
  isplitr
  · iapply kdStorLog_of s ms γs _ _ _ $$ Hrec He0
  isplitl [Hents]
  · iapply kdStorLog_of s ms γs _ _ _ $$ Hrec Hents
  iapply kdStorEnd_of s ms γs _ $$ Hrec
  iexact Hend

end api

end kvdurable
end EtcdGrove
end Perennial
