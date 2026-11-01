/-
Lean-first (no Rocq counterpart).

# The store's storage at raft's node API (2026-10-29, kvreconf's adequacy, helper T1)

What the rest of kvreconf uses of `*kvreconf.Storage` (`KvrStorage.lean`'s vocabulary):

- **the promoted methods** (`Storage.wp_X`): `MemoryStorage.X.spec` restated at the wrapper (the
  method resolved on `*Storage`, which loads the embedded `MemoryStorage` and calls its method), with
  the wrapper's record `kvrStorRec s ms γs` added to the precondition, for the methods raft and the
  replica call: `FirstIndex`, `LastIndex`, `Term`, `Entries`, `Append`, `ApplySnapshot`,
  `SetHardState`, `CreateSnapshot`, `Compact`;
- **the contract** (`kvrStorage_isStorage`, under `kvrStorageModel`): a registered wrapper whose
  `MemoryStorage` has its invariant at `kvrJ γ id` is node `id`'s storage (`isStorage`), as raft's
  `memStorage_isStorageP` is proved (`Snapshot` is the wrapper's own, `Storage.Snapshot.spec`);
- **the boot premise** (`kvr_bootStorage`): what `RestartNode` asks of a fresh storage
  (`bootStorage`), from what `NewMemoryStorage` gives; its `InitialState` allocates the invariant;
- **the records of a new wrapper** (`kvrStor_alloc`), from its fields as allocated.

The contract and the boot premise need the package's `isPkgInit` (the wrapper's `Snapshot` and
`InitialState` specs take it).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorage
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage__InitialState
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage__Snapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__LastIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Term
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Entries
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section promoted
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [KvrStor GF]

theorem Storage.wp_FirstIndex (wp : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (c : Nat) :
  {{ kvrStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memCompacted γs c) }}
    (App (Val (s @!! go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty @!! go!"FirstIndex")) (Val #()))
  {{ (fi : w64), RET (PairV #fi #interface.nil);
      ⌜c + 1 ≤ uint.nat fi⌝ ∗ memCompacted γs (uint.nat fi - 1) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvrStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs c $$ [HP] as %fi HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem Storage.wp_LastIndex (wp : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (e : Nat) :
  {{ kvrStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗ memEnd γs e) }}
    (App (Val (s @!! go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty @!! go!"LastIndex")) (Val #()))
  {{ (li : w64), RET (PairV #li #interface.nil); memEnd γs e ∗ ⌜uint.nat li + 1 = e⌝ }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvrStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs e  $$ [HP] as %li HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem Storage.wp_Term (wp : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) (i0 : w64)
    (ec : GoInterface) :
  {{ kvrStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memLog γs k dq es ∗ ⌜k ≤ uint.nat i0 ∧ uint.nat i0 < k + es.length⌝ ∗
      globalAddr ErrCompacted ↦□ ec) }}
    (App (Val (s @!! go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty @!! go!"Term")) (Val #i0))
  {{ (t : w64) (err : GoInterface), RET (PairV #t #err);
      memLog γs k dq es ∗
      (⌜err = interface.nil ∧ (fun e : EntryM => e.Term') <$> es[uint.nat i0 - k]? = some t⌝ ∨
       (⌜err = ec⌝ ∗ memCompacted γs (uint.nat i0 + 1))) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvrStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs k dq es i0 ec  $$ [HP] as %t %err HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem Storage.wp_Entries (wp : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq1 dq2 : DFrac) (a b : List EntryM)
    (lo hi maxSize : w64) (ec : GoInterface) :
  {{ kvrStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memLog γs k dq1 a ∗ memLog γs (k + a.length) dq2 b ∗
      ⌜k ≤ uint.nat lo ∧ uint.nat lo < uint.nat hi ∧ uint.nat hi ≤ k + a.length + b.length⌝ ∗
      globalAddr ErrCompacted ↦□ ec) }}
    (App (App (App (Val (s @!! go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty @!! go!"Entries")) (Val #lo)) (Val #hi)) (Val #maxSize))
  {{ (sl : GoSlice) (es : List EntryM) (err : GoInterface), RET (PairV #sl #err);
      memLog γs k dq1 a ∗ memLog γs (k + a.length) dq2 b ∗
      ((⌜err = ec⌝ ∗ memCompacted γs (uint.nat lo)) ∨
       (⌜err = interface.nil⌝ ∗ entsRO sl es ∗
        ⌜es ≠ [] ∧ sl.cap = sl.len ∧
          es <+: ((a ++ b).drop (uint.nat lo - k)).take (uint.nat hi - uint.nat lo)⌝)) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvrStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs k dq1 dq2 a b lo hi maxSize ec  $$ [HP] as %sl %es %err HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem Storage.wp_Append (wp : MemoryStorage.Append.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (k : Nat) (old es : List EntryM) (sl : GoSlice) (dq : DFrac)
    (h1 : ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = k + j)
    (h2 : k + es.length ≤ 2^61) :
  {{ kvrStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) old ∗ memEnd γs (k + old.length)) ∗
      entsPts sl dq es) }}
    (App (Val (s @!! go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty @!! go!"Append")) (Val #sl))
  {{ RET #interface.nil; entsPts sl dq es ∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length)) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvrStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs k old es sl dq h1 h2 $$ [HP] as  HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem Storage.wp_ApplySnapshot (wp : MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (J : MemJust GF) (j : Nat) (old : List EntryM) (sp : Loc)
    (dq : DFrac) (sv : SnapshotM) (eood : GoInterface)
    (h1 : j ≤ uint.nat sv.Metadata'.Index')
    (h2 : uint.nat sv.Metadata'.Index' < 2^61) :
  {{ kvrStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorInvP ms γs J ∗
      memLog γs j (DFrac.own 1) old ∗ memEnd γs (j + old.length) ∗
      J.B (uint.nat sv.Metadata'.Index') ∗ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index') ∗
      snapArg sp dq sv ∗ memSnapLb γs 0 ∗ globalAddr ErrSnapOutOfDate ↦□ eood) }}
    (App (Val (s @!! go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty @!! go!"ApplySnapshot")) (Val #sp))
  {{ RET #interface.nil; ownSnapM sp dq sv ∗
      memCompacted γs (uint.nat sv.Metadata'.Index') ∗
      memLog γs (uint.nat sv.Metadata'.Index') DFrac.discard [memDummy sv] ∗
      memEnd γs (uint.nat sv.Metadata'.Index' + 1) ∗ memSnapLb γs (uint.nat sv.Metadata'.Index') }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvrStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs J j old sp dq sv eood h1 h2 $$ [HP] as  HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem Storage.wp_SetHardState (wp : MemoryStorage.SetHardState.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (hs : HardStateM) (st : Loc) (hs' : HardStateM) :
  {{ kvrStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      memStorMeta ms γs hs ∗ hsOpt st hs') }}
    (App (Val (s @!! go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty @!! go!"SetHardState")) (Val #st))
  {{ RET #interface.nil; memStorMeta ms γs hs' }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvrStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs hs st hs'  $$ [HP] as  HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem Storage.wp_CreateSnapshot (wp : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (J : MemJust GF) (i : w64) (e : EntryM) (cs : Loc)
    (dq : DFrac) (c : ConfStateM) (data : GoSlice) (bs : List w8) (eood : GoInterface) :
  {{ kvrStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorInvP ms γs J ∗
      memLog γs (uint.nat i) DFrac.discard [e] ∗
      J.SV (memSnapMade i e.Term' c bs) ∗ J.DL (uint.nat i) ∗
      memSnapLb γs 0 ∗ ownCSM cs dq c ∗ data ↦* bs ∗
      globalAddr ErrSnapOutOfDate ↦□ eood) }}
    (App (App (App (Val (s @!! go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty @!! go!"CreateSnapshot")) (Val #i)) (Val #cs)) (Val #data))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      ownCSM cs dq c ∗ memSnapLb γs (uint.nat i) ∗
      ((⌜err = interface.nil⌝ ∗ ownSnapM snap (DFrac.own 1) (memSnapMade i e.Term' c bs)) ∨
       (⌜snap = null ∧ err = eood⌝ ∗ data ↦* bs)) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvrStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs J i e cs dq c data bs eood  $$ [HP] as %snap %err HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem Storage.wp_Compact (wp : MemoryStorage.Compact.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (J : MemJust GF) (x : w64) (ecomp : GoInterface) :
  {{ kvrStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorInvP ms γs J ∗
      ((∃ (e : EntryM), memLog γs (uint.nat x) DFrac.discard [e]) ∨ memCompacted γs (uint.nat x)) ∗
      J.B (uint.nat x) ∗ memSnapLb γs (uint.nat x) ∗ globalAddr ErrCompacted ↦□ ecomp) }}
    (App (Val (s @!! go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty @!! go!"Compact")) (Val #x))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil ∨ err = ecomp⌝ ∗ memCompacted γs (uint.nat x) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvrStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs J x ecomp $$ [HP] as %err HQ
  · iexact HP
  iapply HΦ
  iexact HQ

end promoted

section api
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [KvrStor GF] [AllG GF]
attribute [local instance] kvrStorageModel

/-- `kvrJ`'s compaction justification is the API's (`storBnd`). -/
theorem kvrJ_bnd (γ : Cluster) (id : w64) (c : Nat) :
    memBnd (kvrJ (GF := GF) γ id) c ⊢ storBnd γ id c := by
  unfold memBnd storBnd kvrJ; exact .rfl

theorem kvrJ_B0 (γ : Cluster) (id : w64) : ⊢ (kvrJ (GF := GF) γ id).B 0 := by
  unfold kvrJ
  iintro
  ileft; iapply nodeAppliedLb_zero

/-- **The store's storage meets node `id`'s storage contract** (under `kvrStorageModel`). -/
theorem kvrStorage_isStorage
    (wp_Snapshot : Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (γ : Cluster) (id : w64) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf -∗
      kvrStorRec s ms γs -∗ memStorInvP ms γs (kvrJ γ id) -∗
      isStorage γ id (kvrStorIface s) := by
  iintro #Hpkg #Hrec #Hinv
  ihave #Hl : memStorLock ms γs $$ []
  · iunfold memStorInvP at Hinv; icases Hinv with ⟨#Hl, -⟩; iexact Hl
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  unfold isStorage isStorageP
  iexists (interface.mk (go.GoType.PointerType
    github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty) #s)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %e
    imodintro
    iintro %Φ He HΦ
    ihave He := kvrStorEnd_to s ms γs e $$ Hrec He
    wp_apply Storage.wp_LastIndex wp_LastIndex s ms γs e $$ [$Hrec $Hinit $Hl $He] as %li ⟨He, %Hli⟩
    iapply HΦ
    ihave He := kvrStorEnd_of s ms γs e $$ Hrec He
    iframe He
    ipureintro; exact Hli
  isplitr
  · iintro %k %dq %es %i0 %ec
    imodintro
    iintro %Φ ⟨H, %Hr, #Hec⟩ HΦ
    ihave H := kvrStorLog_to s ms γs k dq es $$ Hrec H
    wp_apply Storage.wp_Term wp_Term s ms γs k dq es i0 ec $$ [$Hrec $Hinit $Hl $H $Hec]
      as %t %err ⟨H, Ht⟩
    · ipureintro; exact Hr
    iapply HΦ
    ihave H := kvrStorLog_of s ms γs k dq es $$ Hrec H
    iframe H
    icases Ht with (%Ht | ⟨%Ht, #Hc⟩)
    · ileft; ipureintro; exact Ht
    · iright
      isplitr
      · ipureintro; exact Ht
      iapply kvrStorCompacted_of s ms γs _ $$ Hrec Hc
  isplitr
  · iintro %k %dq1 %dq2 %a %b %lo %hi %maxSize %ec
    imodintro
    iintro %Φ ⟨Ha, Hb, %Hr, #Hec⟩ HΦ
    ihave Ha := kvrStorLog_to s ms γs k dq1 a $$ Hrec Ha
    ihave Hb := kvrStorLog_to s ms γs (k + a.length) dq2 b $$ Hrec Hb
    wp_apply Storage.wp_Entries wp_Entries s ms γs k dq1 dq2 a b lo hi maxSize ec
      $$ [$Hrec $Hinit $Hl $Ha $Hb $Hec] as %sl %es %err ⟨Ha, Hb, Hres⟩
    · ipureintro; exact Hr
    iapply HΦ $$ %sl %es %err
    ihave Ha := kvrStorLog_of s ms γs k dq1 a $$ Hrec Ha
    ihave Hb := kvrStorLog_of s ms γs (k + a.length) dq2 b $$ Hrec Hb
    iframe Ha Hb
    icases Hres with (⟨%He, #Hc⟩ | Hres)
    · ileft
      isplitr
      · ipureintro; exact He
      iapply kvrStorCompacted_of s ms γs _ $$ Hrec Hc
    · iright; iexact Hres
  isplitr
  · iintro %c
    imodintro
    iintro %Φ #Hc HΦ
    ihave #Hc := kvrStorCompacted_to s ms γs c $$ Hrec Hc
    wp_apply Storage.wp_FirstIndex wp_FirstIndex s ms γs c $$ [$Hrec $Hinit $Hl $Hc]
      as %fi ⟨%Hfi, #Hc'⟩
    iapply HΦ
    isplitr
    · ipureintro; exact Hfi
    iapply kvrStorCompacted_of s ms γs _ $$ Hrec Hc'
  isplitr
  · iintro %c %esu
    imodintro
    iintro %Φ ⟨#Hc, #Hesu⟩ HΦ
    ihave #Hc := kvrStorCompacted_to s ms γs c $$ Hrec Hc
    wp_apply wp_Snapshot s ms γs (kvrJ γ id) c esu $$ [$Hpkg $Hrec $Hinv $Hc $Hesu]
      as %snap %err Hres
    iapply HΦ
    iexact Hres
  isplitr
  · iintro !> %c #Hc
    ihave #Hc := kvrStorCompacted_to s ms γs c $$ Hrec Hc
    imod memCompacted_bound ms γs (kvrJ γ id) c $$ Hinv Hc with Hb
    imodintro
    iapply kvrJ_bnd γ id c $$ Hb
  iintro !> %k %dq %es H
  ihave H := kvrStorLog_to s ms γs k dq es $$ Hrec H
  iunfold memLog at H
  icases H with ⟨H, %Hb⟩
  isplitr
  · ipureintro; exact Hb
  iapply kvrStorLog_of s ms γs k dq es $$ Hrec
  iunfold memLog
  iframe H
  ipureintro; exact Hb

/-- **The store's storage before `RestartNode`** (`RestartNode`'s `bootStorage` premise), from what
`NewMemoryStorage` gave of its `MemoryStorage` and the wrapper's records: `FirstIndex` is `1` (the
storage is fresh, `memStorFresh_compacted`), `LastIndex` `0`, and `InitialState` gives the hard
state, the bootstrap conf state, and (allocating the storage's invariant) the contract. The frame
`Q` is the hard state's metadata and the invariant. -/
theorem kvr_bootStorage
    (wp_InitialState : Storage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (s ms bp : Loc) (γs : MemStorNames) (hs : HardStateM) (csm : ConfStateM)
    (γ : Cluster) (id : w64) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf -∗
      kvrStorRec s ms γs -∗ kvrStorBoot s bp csm -∗
      memStorLock ms γs -∗ memStorFresh ms γs -∗ memStorMeta ms γs hs -∗
      memLog γs 0 DFrac.discard [zero_val EntryM] -∗ memEnd γs 1 -∗
      bootStorage γ id (kvrStorIface s) hs csm
        iprop(memStorMeta ms γs hs ∗ memStorInvP ms γs (kvrJ γ id)) := by
  iintro #Hpkg #Hrec #Hboot #Hl Hfresh Hmeta #Hlog He
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  unfold bootStorage
  iexists (interface.mk (go.GoType.PointerType
    github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty) #s)
  iexists iprop(memStorFresh ms γs ∗ memStorMeta ms γs hs ∗ memEnd γs 1)
  isplitr
  · ipureintro; rfl
  isplitl [Hfresh Hmeta He]
  · iframe Hfresh Hmeta He
  isplitr
  · iintro !> %Φ ⟨Hfresh, Hmeta, He⟩ HΦ
    wp_apply Storage.wp_FirstIndex wp_FirstIndex s ms γs 0 $$ [$Hrec $Hinit $Hl]
      as %fi ⟨%Hfi, #Hc⟩
    · iapply memCompacted_zero
    icases memStorFresh_compacted ms γs _ $$ [$Hfresh $Hc] with ⟨%H0, Hfresh⟩
    have Hfi1 : fi = W64 1 := by word
    subst Hfi1
    iapply HΦ
    iframe Hfresh Hmeta He
  isplitr
  · iintro !> %Φ ⟨Hfresh, Hmeta, He⟩ HΦ
    wp_apply Storage.wp_LastIndex wp_LastIndex s ms γs 1 $$ [$Hrec $Hinit $Hl $He]
      as %li ⟨He, %Hli⟩
    have Hli0 : li = W64 0 := by word
    subst Hli0
    iapply HΦ
    iframe Hfresh Hmeta He
  iintro !> %Φ ⟨Hfresh, Hmeta, He⟩ HΦ
  iapply wp_fupd
  wp_apply wp_InitialState s ms bp γs hs csm $$ [$Hpkg $Hrec $Hboot $Hmeta $Hfresh]
    as %hp %cs ⟨#Hhs, Hmeta, Hfresh, Hcs⟩
  imod csPts_persist cs (DFrac.own 1) csm false $$ Hcs with #Hcs
  imodintro
  iapply HΦ $$ %hp %cs %false
  iframe Hhs Hcs Hmeta
  imod memStorInvP_alloc ms γs (kvrJ γ id) ⊤ $$ Hl Hfresh [] with #Hinv
  · iapply kvrJ_B0 γ id
  imodintro
  isplitr
  · iapply kvrStorage_isStorage wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term wp_Entries
      s ms γs γ id $$ Hpkg Hrec Hinv
  iframe Hinv
  iexists (zero_val EntryM)
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply kvrStorLog_of s ms γs 0 DFrac.discard [zero_val EntryM] $$ Hrec Hlog
  iapply kvrStorEnd_of s ms γs 1 $$ Hrec He

/-- **A new wrapper's records** (`&Storage{MemoryStorage: ms, boot: bp}`, its two fields as
allocated; the bootstrap conf state read-only): the registry's record (`kvr_register`) and the boot
record, both persistent. -/
theorem kvrStor_alloc (s ms bp : Loc) (γs : MemStorNames) (csm : ConfStateM) (E : CoPset)
    (HE : ↑kvrStorN ⊆ E) :
    ⊢ kvrStorInv (GF := GF) -∗
      s.[github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage, go!"MemoryStorage"] ↦ ms -∗
      s.[github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage, go!"boot"] ↦ bp -∗
      ownCSM bp DFrac.discard csm ={E}=∗
      kvrStorRec s ms γs ∗ kvrStorBoot s bp csm := by
  iintro #Hinv Hm Hb #Hcs
  imod kvrStor_register s ms γs E HE $$ Hinv Hm with #Hrec
  imod (typedPointsto_dfractional (GF := GF) _ bp).dfractional_persist _ $$ Hb with #Hb
  imodintro
  iframe Hrec
  iunfold kvrStorBoot
  iframe Hb Hcs

end api

end kvreconf
end EtcdGrove
end Perennial
