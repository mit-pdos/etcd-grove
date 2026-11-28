/-
Lean-first (no Rocq counterpart). #33 parity B1 (S4's `RunClusterStorage.lean`, restored for
`node.start`): **a node's storage at raft's start**.

What `NewRawNode.restartAtSpec` takes of the `bootStorage` `node.start` builds over a fresh
`MemoryStorage` holding the node's disk (kvdurable's `KdStorageApi.lean`, at the harness's wrapper):

- **the storage model** `antStorageModelNC`: `antStorageModel`'s `storLog`/`storEnd` (so a node's
  `antStorBridge` is the same), and `storCompacted st c` either `c = 0` or a `MemoryStorage`'s
  compaction point under an attached invariant of `antJ` (whose compaction justification is `0`).
  `NewRawNode.restartAtSpec` takes `storCapF … 0` (the storage never compacted) *before* the storage
  is attached (raft attaches it in `InitialState`'s continuation, `restartStorage`), when the
  `MemoryStorage`'s compaction list is in the detached token raft holds; with `antStorageModel`'s
  `storCompacted` (any registered wrapper's `memCompacted`) nothing persistent bounds it then. Here a
  compaction point past `0` names the attached invariant, which bounds it (`memCompacted_bound`).
  `RunCluster` makes it the instance of the run (`letI`, after allocating the registry).
- **the justifications** `antJ γ K`: `memStorJ`'s, the compaction point `0` (the harness never calls
  `Compact`).
- **the contract** (`antStorage_isStorage`), **the start premise** (`ant_restartStorage`, at the
  contents `bootContents h es`: the disk's hard state `h` and entries `es` from index 1, no snapshot,
  the voters' conf state), **the cap** (`antStor_storCapF`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.AntStorage
public import Proof.go_etcd_io.raft.v3.RawNodeStartSpec
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage__InitialState
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage__Snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage__LastIndex
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage__FirstIndex
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage__Term
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage__Entries

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section just
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The harness's justifications** for the `MemoryStorage` of key `K`: `memStorJ`'s, at the
compaction point `0` only (nothing compacts it). -/
def antJ (γ : Cluster) (K : GName) : MemJust GF where
  SV := snapshotValid γ
  B k := iprop(nodeAppliedLb γ K k ∗ ⌜k = 0⌝)
  DL := nodeCommitLb γ K
  SV_pers := fun sv => by infer_instance
  B_pers := fun k => by infer_instance
  B_timeless := fun k => by infer_instance
  DL_pers := fun i => by infer_instance

/-- `antJ`'s compaction justification is the API's (`storBnd`), and at `0`. -/
theorem antJ_bnd (γ : Cluster) (K : GName) (c : Nat) (htr : Cluster.trace γ = none) :
    memBnd (antJ (GF := GF) γ K) c ⊢ storBnd γ K c ∗ ⌜c = 0⌝ := by
  unfold memBnd antJ
  iintro ⟨%k, %Hk, #Hl, %H0⟩
  subst H0
  isplitl
  · iapply storBnd_intro_untraced γ K 0 c htr (fun _ => Nat.zero_le 1) $$ Hl
    ipureintro; exact Hk
  ipureintro; omega

/-- `storCompacted` of `antStorageModelNC`: `0`, or a `MemoryStorage`'s compaction point under its
attached invariant at `antJ`. -/
def antStorCompactedNC (_st : Storage) (c : Nat) : IProp GF :=
  iprop(⌜c = 0⌝ ∨ ∃ (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName),
    memStorInvP ms γs (antJ γ K) ∗ memCompacted γs c)

instance antStorCompactedNC_persistent (st : Storage) (c : Nat) :
    Persistent (antStorCompactedNC (GF := GF) st c) := by
  unfold antStorCompactedNC; infer_instance

theorem antStorCompactedNC_mono (st : Storage) (c c' : Nat) (h : c' ≤ c) :
    antStorCompactedNC (GF := GF) st c ⊢ antStorCompactedNC st c' := by
  unfold antStorCompactedNC
  iintro (%H | ⟨%ms, %γs, %γ, %K, #Hi, #Hc⟩)
  · ileft; ipureintro; omega
  iright
  iexists ms, γs, γ, K
  iframe Hi
  iapply memCompacted_mono γs c c' h $$ Hc

/-- A compaction point is `0`. -/
theorem antStorCompactedNC_zero (st : Storage) (c : Nat) :
    ⊢ antStorCompactedNC (GF := GF) st c ={⊤}=∗ ⌜c = 0⌝ := by
  unfold antStorCompactedNC
  iintro (%H | ⟨%ms, %γs, %γ, %K, #Hi, #Hc⟩)
  · imodintro; ipureintro; exact H
  imod memCompacted_bound ms γs (antJ γ K) c $$ Hi Hc with Hb
  unfold memBnd antJ
  icases Hb with ⟨%k, %Hk, -, %H0⟩
  imodintro; ipureintro; omega

end just

section model
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [AntStor GF]

/-- **The harness's storage model** (see the file header): `antStorageModel`'s logs and ends, and
compaction points `antStorCompactedNC`. A `def`, made an instance locally. -/
@[instance_reducible]
def antStorageModelNC : StorageModel GF where
  storLog := antStorLogI
  storEnd := antStorEndI
  storCompacted := antStorCompactedNC
  storLog_app := antStorLogI_app
  storLog_frac := antStorLogI_frac
  storLog_valid := antStorLogI_valid
  storLog_agree := antStorLogI_agree
  storLog_persist := antStorLogI_persist
  storLog_persistent := fun st k es => by unfold antStorLogI; infer_instance
  storLog_nil := fun st k dq => by unfold antStorLogI; iintro; ileft; ipureintro; rfl
  storEnd_excl := antStorEndI_excl
  storCompacted_persistent := fun st c => by infer_instance
  storCompacted_zero := fun st => by unfold antStorCompactedNC; iintro; ileft; ipureintro; rfl
  storCompacted_mono := antStorCompactedNC_mono

attribute [local instance] antStorageModelNC

/-- `antStorageModelNC`'s log is `antStorageModel`'s. -/
theorem antNC_log_to (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ antStorRec (GF := GF) s ms γs -∗ storLog (antStorIface s) k dq es -∗ memLog γs k dq es :=
  antStorLog_to (GF := GF) s ms γs k dq es

theorem antNC_log_of (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ antStorRec (GF := GF) s ms γs -∗ memLog γs k dq es -∗ storLog (antStorIface s) k dq es :=
  antStorLog_of (GF := GF) s ms γs k dq es

theorem antNC_end_to (s ms : Loc) (γs : MemStorNames) (e : Nat) :
    ⊢ antStorRec (GF := GF) s ms γs -∗ storEnd (antStorIface s) e -∗ memEnd γs e :=
  antStorEnd_to (GF := GF) s ms γs e

theorem antNC_end_of (s ms : Loc) (γs : MemStorNames) (e : Nat) :
    ⊢ antStorRec (GF := GF) s ms γs -∗ memEnd γs e -∗ storEnd (antStorIface s) e :=
  antStorEnd_of (GF := GF) s ms γs e

/-- **A registered wrapper's interface has the bridge** under `antStorageModelNC`. -/
theorem antNC_bridge (s ms : Loc) (γs : MemStorNames) :
    ⊢ antStorRec (GF := GF) s ms γs -∗ antStorBridge (antStorIface s) γs :=
  antStor_bridge (GF := GF) s ms γs

/-- A compaction point under the attached invariant. -/
theorem antNC_compacted_of (st : Storage) (ms : Loc) (γs : MemStorNames) (γ : Cluster) (K : GName)
    (c : Nat) :
    ⊢ memStorInvP (GF := GF) ms γs (antJ γ K) -∗ memCompacted γs c -∗ storCompacted st c := by
  iintro #Hi #Hc
  ihave H : antStorCompactedNC (GF := GF) st c $$ []
  · unfold antStorCompactedNC
    iright; iexists ms, γs, γ, K; iframe Hi Hc
  iexact H

/-- **The storage is never compacted** (`storCapF … 0`, `NewRawNode.emptyStartForm`'s). -/
theorem antStor_storCapF (st : Storage) : ⊢ storCapF (GF := GF) st 0 := by
  unfold storCapF
  iintro !> %c Hc
  imod antStorCompactedNC_zero st c $$ Hc with %H
  imodintro; ipureintro; omega

/-- **The harness's storage meets the storage contract of key `K`** (under `antStorageModelNC`;
kvdurable's `kdStorage_isStorage`): a registered wrapper whose `MemoryStorage` has its invariant at
`antJ γ K`, in an untraced cluster with no bound on proposed data. -/
theorem antStorage_isStorage
    (wp_Snapshot : bootStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : bootStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : bootStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : bootStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : bootStorage.Entries.spec (GF := GF) (hG := hG))
    (s ms : Loc) (vs : List w64) (γs : MemStorNames) (γ : Cluster) (K : GName)
    (htr : Cluster.trace γ = none) (hmd : γ.maxData = none) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis -∗
      antStorRec s ms γs -∗ bootStorRec s ms vs -∗ memStorInvP ms γs (antJ γ K) -∗
      isStorage γ K (antStorIface s) := by
  iintro #Hpkg #Hrec #Hboot #Hinv
  ihave #Hl : memStorLock ms γs $$ []
  · iunfold memStorInvP at Hinv; icases Hinv with ⟨#Hl, -⟩; iexact Hl
  unfold isStorage isStorageP
  rw [hmd, Option.isSome_none]
  iexists ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #s⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %e
    imodintro
    iintro %Φ He HΦ
    ihave He := antNC_end_to s ms γs e $$ Hrec He
    wp_apply wp_LastIndex s ms vs γs e $$ [$Hpkg $Hboot $Hl $He] as %li ⟨He, %Hli⟩
    iapply HΦ
    ihave He := antNC_end_of s ms γs e $$ Hrec He
    iframe He
    ipureintro; exact Hli
  isplitr
  · iintro %k %dq %es %i0 %ec
    imodintro
    iintro %Φ ⟨H, %Hr, #Hec⟩ HΦ
    ihave H := antNC_log_to s ms γs k dq es $$ Hrec H
    wp_apply wp_Term s ms vs γs k dq es i0 ec $$ [$Hpkg $Hboot $Hl $H $Hec] as %t %err ⟨H, Ht⟩
    · ipureintro; exact Hr
    iapply HΦ
    ihave H := antNC_log_of s ms γs k dq es $$ Hrec H
    iframe H
    icases Ht with (%Ht | ⟨%Ht, #Hc⟩)
    · ileft; ipureintro; exact Ht
    · iright
      isplitr
      · ipureintro; exact Ht
      iapply antNC_compacted_of _ ms γs γ K _ $$ Hinv Hc
  isplitr
  · iintro %k %dq1 %dq2 %a %b %lo %hi %maxSize %ec
    imodintro
    iintro %Φ ⟨Ha, Hb, %Hr, #Hec⟩ HΦ
    ihave Ha := antNC_log_to s ms γs k dq1 a $$ Hrec Ha
    ihave Hb := antNC_log_to s ms γs (k + a.length) dq2 b $$ Hrec Hb
    wp_apply wp_Entries s ms vs γs k dq1 dq2 a b lo hi maxSize ec
      $$ [$Hpkg $Hboot $Hl $Ha $Hb $Hec] as %sl %es %err ⟨Ha, Hb, Hres⟩
    · ipureintro; exact Hr
    iapply HΦ $$ %sl %es %err
    ihave Ha := antNC_log_of s ms γs k dq1 a $$ Hrec Ha
    ihave Hb := antNC_log_of s ms γs (k + a.length) dq2 b $$ Hrec Hb
    iframe Ha Hb
    icases Hres with (⟨%He, #Hc⟩ | ⟨%He, ⟨%cs, #Hcs, %Hcm⟩, %Hr'⟩)
    · ileft
      isplitr
      · ipureintro; exact He
      iapply antNC_compacted_of _ ms γs γ K _ $$ Hinv Hc
    · iright
      isplitr; · ipureintro; exact He
      isplitr
      · iexists cs
        ihave Hcs' := entsPtsC_unsize _ _ _ _ $$ Hcs
        iframe Hcs'
        ipureintro; exact ⟨Hcm.1, fun h => absurd h (by simp)⟩
      ipureintro; exact ⟨Hr'.1, Hr'.2.1, Hr'.2.2.1⟩
  isplitr
  · iintro %c
    imodintro
    iintro %Φ #Hc HΦ
    imod antStorCompactedNC_zero _ c $$ Hc with %Hc0
    subst Hc0
    ihave #Hm0 : memCompacted γs 0 $$ []
    · unfold memCompacted; ileft; ipureintro; rfl
    wp_apply wp_FirstIndex s ms vs γs 0 $$ [$Hpkg $Hboot $Hl $Hm0] as %fi ⟨%Hfi, #Hc'⟩
    iapply HΦ
    isplitr
    · ipureintro; exact Hfi
    iapply antNC_compacted_of _ ms γs γ K _ $$ Hinv Hc'
  isplitr
  · iintro %c %esu
    imodintro
    iintro %Φ ⟨#Hc, #Hesu⟩ HΦ
    imod antStorCompactedNC_zero _ c $$ Hc with %Hc0
    subst Hc0
    ihave #Hm0 : memCompacted γs 0 $$ []
    · unfold memCompacted; ileft; ipureintro; rfl
    wp_apply wp_Snapshot s ms vs γs (antJ γ K) none 0 none esu $$ [$Hpkg $Hboot $Hm0 $Hesu]
      as %snap %err ⟨-, %Herr, %sv, Hs, %Hsv, Hv⟩
    · iapply memStorAt_none_intro $$ Hinv
      iempintro
    iapply HΦ
    ihave Hs := ownSnapW_E $$ Hs
    ihave Hs := ownSnapE_weaken $$ Hs
    iright
    isplitr; · ipureintro; exact Herr
    iexists sv
    iframe Hs
    isplitr; · ipureintro; exact Hsv.1
    iexact Hv
  isplitr
  · iintro !> %c #Hc
    imod antStorCompactedNC_zero _ c $$ Hc with %Hc0
    subst Hc0
    ihave #Hm0 : memCompacted γs 0 $$ []
    · unfold memCompacted; ileft; ipureintro; rfl
    imod memCompacted_bound ms γs (antJ γ K) 0 $$ Hinv Hm0 with Hb
    imodintro
    ihave ⟨Hb, -⟩ := antJ_bnd γ K 0 htr $$ Hb
    iexact Hb
  iintro !> %k %dq %es H
  ihave H := antNC_log_to s ms γs k dq es $$ Hrec H
  iunfold memLog at H
  icases H with ⟨H, %Hb⟩
  isplitr
  · ipureintro; exact Hb
  iapply antNC_log_of s ms γs k dq es $$ Hrec
  iunfold memLog
  iframe H
  ipureintro; exact Hb

/-- The storage contents of a node's disk at the start (B1: no snapshot): the hard state `h`, the
entries `es` from index 1 (boundary `base0`). -/
def bootContents (h : HardStateM) (es : List EntryM) : StorContents := ⟨h, none, base0, es⟩

/-- **A node's storage before `NewRawNode`** (`NewRawNode.restartAtSpec`'s `restartStorage` premise at
`bootContents h es`, the voters' conf state, raft's applied index `0`; kvdurable's
`kd_restartStorage`): from what `memoryOf` gave (the disk's hard state `h`, its entries `es` from
index 1), the wrapper registered. The frame `F` is the client's, from the hard state's metadata and
the invariant at the key (`HF`). The freeze point is `0`: nothing frozen. -/
theorem ant_restartStorage
    (wp_InitialState : bootStorage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : bootStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : bootStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : bootStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : bootStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : bootStorage.Entries.spec (GF := GF) (hG := hG))
    (s ms : Loc) (vs : List w64) (γs : MemStorNames) (γ : Cluster) (F : GName → IProp GF)
    (h : HardStateM) (es : List EntryM) (hlen : es.length < 2 ^ 63)
    (htr : Cluster.trace γ = none) (hmd : γ.maxData = none) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis -∗
      antStorRec s ms γs -∗ bootStorRec s ms vs -∗ memStorLock ms γs -∗
      memLog γs 0 DFrac.discard [zero_val EntryM] -∗ memLog γs 1 (DFrac.own 1) es -∗
      memEnd γs (1 + es.length) -∗
      memStorMeta ms γs h -∗ memStorFresh ms γs 0 memSnapEmpty -∗
      (∀ K : GName, memStorMeta ms γs h -∗ memStorInvP ms γs (antJ γ K) -∗ F K) -∗
      restartStorage γ (antStorIface s) (bootContents h es) (bootConfState vs memSnapEmpty) 0 F := by
  iintro #Hpkg #Hrec #Hboot #Hl #He0 Hlog Hend Hmeta Hfresh HF
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  ihave #Hini := isInitialized_access $$ Hraft
  iunfold isInitialized at Hini
  icases Hini with ⟨%_e1, %_e2, %_e3, %esu, %_e5, %_g, %_l, %_r, %_e6, %_e7, -, -, #Hesu, -⟩
  have hb : (bootContents h es).b = 0 := by simp [bootContents, StorContents.b, base0]
  have hl : (bootContents h es).last = es.length := by
    simp [bootContents, StorContents.last, StorContents.b, base0]
  have he : (bootContents h es).ents = es := rfl
  have hh : (bootContents h es).hs = h := rfl
  have hba : (bootContents h es).base = base0 := rfl
  unfold restartStorage storHolds
  simp only [hb, hl, he, hh, hba, Nat.zero_sub, Nat.sub_zero, List.take_zero, List.drop_zero,
    Nat.zero_add, Nat.max_self]
  iexists ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #s⟩
  iexists iprop(memStorFresh ms γs 0 memSnapEmpty ∗ memStorMeta ms γs h ∗ memEnd γs (1 + es.length) ∗
    memLog γs 1 (DFrac.own 1) es ∗
    (∀ K : GName, memStorMeta ms γs h -∗ memStorInvP ms γs (antJ γ K) -∗ F K))
  iexists 0
  simp only [List.take_zero, List.drop_zero]
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; exact ⟨Nat.le_refl 0, Nat.zero_le _⟩
  isplitl [Hfresh Hmeta Hend Hlog HF]
  · iframe
  isplitr
  · -- FirstIndex: `1` (detached at `0`)
    iintro !> %Φ ⟨Hfresh, HR⟩ HΦ
    ihave #Hm0 : memCompacted γs 0 $$ []
    · unfold memCompacted; ileft; ipureintro; rfl
    wp_apply wp_FirstIndex s ms vs γs 0 $$ [$Hpkg $Hboot $Hl $Hm0] as %fi ⟨%Hfi, #Hc'⟩
    ihave ⟨%Hle, Hfresh⟩ := memStorFresh_compacted ms γs _ _ _ $$ [$Hfresh $Hc']
    have Hfi' : fi = W64 (((0 : Nat) : Int) + 1) := by word
    subst Hfi'
    iapply HΦ
    iframe
  isplitr
  · -- LastIndex: `|es|`
    iintro !> %Φ ⟨Hfresh, Hmeta, Hend, HR⟩ HΦ
    wp_apply wp_LastIndex s ms vs γs (1 + es.length) $$ [$Hpkg $Hboot $Hl $Hend] as %li ⟨Hend, %Hli⟩
    have Hli' : li = W64 ((es.length : Nat) : Int) := by
      have h1 : uint.nat li = es.length := by omega
      word
    subst Hli'
    iapply HΦ
    iframe
  -- InitialState: detached; its continuation attaches the storage at raft's key
  iintro !> %Φ ⟨Hfresh, Hmeta, Hend, Hlog, HF⟩ HΦ
  wp_apply wp_InitialState s ms vs γs h 0 memSnapEmpty esu
    $$ [$Hpkg $Hboot $Hl $Hmeta $Hfresh $Hesu] as %hp %cs %al ⟨Hhs, Hmeta, Hfresh, Hcs⟩
  iapply HΦ
  isplitl [Hhs]
  · iexact Hhs
  isplitl [Hcs]
  · iexact Hcs
  iintro %K #HAl #HCl
  ihave #HB : □ (∀ k, ⌜k ≤ 0⌝ -∗ (antJ γ K).B k) $$ []
  · iintro !> %k %hk
    simp only [antJ]
    isplitr
    · iapply nodeAppliedLb_mono γ K _ k (by omega) $$ HAl
    ipureintro; omega
  imod memStorInvP_alloc ms γs (antJ γ K) ⊤ 0 memSnapEmpty $$ Hl Hfresh HB [] with #Hinv
  · ileft; ipureintro; rfl
  ihave #Hst := antStorage_isStorage wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term wp_Entries
    s ms vs γs γ K htr hmd $$ Hpkg Hrec Hboot Hinv
  ihave HFK := HF $$ %K Hmeta Hinv
  imodintro
  iframe Hst HFK
  iexists zero_val EntryM
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply StorageModel.storCompacted_zero
  isplitr
  · iapply antNC_log_of s ms γs _ _ _ $$ Hrec He0
  isplitr
  · iapply StorageModel.storLog_nil
  isplitl [Hlog]
  · iapply antNC_log_of s ms γs _ _ _ $$ Hrec Hlog
  rw [Nat.add_comm]
  iapply antNC_end_of s ms γs _ $$ Hrec
  iexact Hend

end model

end AntHarness
end EtcdGrove
end Perennial
