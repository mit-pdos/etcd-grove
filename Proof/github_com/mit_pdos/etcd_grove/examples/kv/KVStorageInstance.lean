/-
Lean-first (no Rocq counterpart).

# `*kv.Storage` at raft's node API (2026-10-30, stage F of the client repair: from kvreconf's
`KvrStorageApi.lean`, kv's names; until then `ownStorage`'s contract over `StorState`)

What the rest of kv uses of `*kv.Storage` (`KvStorage.lean`'s vocabulary):

- **the promoted methods** (`kvStorage.wp_X`): `MemoryStorage.X.spec` restated at the wrapper (the
  method resolved on `*Storage`, which loads the embedded `MemoryStorage` and calls its method), with
  the wrapper's record `kvStorRec s ms γs` added to the precondition, for the methods raft and the
  replica call: `FirstIndex`, `LastIndex`, `Term`, `Entries`, `Append`, `ApplySnapshot`,
  `SetHardState`, `CreateSnapshot`, `Compact`;
- **the contract** (`kvStorage_isStorage`): a registered wrapper whose `MemoryStorage` has its
  invariant at `kvJ γ id` is node `id`'s storage (`isStorage`), as raft's `memStorage_isStorageP`
  is proved (`Snapshot` is the wrapper's own, `kv.Storage.Snapshot.spec`);
- **the boot premise** (`kvStorage_bootStorage`): what `RestartNode` asks of a fresh storage
  (`bootStorage`), from what `NewMemoryStorage` gives. kv's `InitialState` (`kv.go`) never calls
  `MemoryStorage.InitialState` (it answers `HardState{}` and the wrapper's voters), so the
  storage's invariant is allocated inside `bootStorage`'s update, from `memStorLock ∗
  memStorFresh` (the frame).

The contract and the boot premise need the package's `isPkgInit` (the wrapper's `Snapshot` and
`InitialState` specs take it).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.KvStorage
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Storage__InitialState
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Storage__Snapshot
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

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section promoted
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

theorem kvStorage.wp_FirstIndex (wp : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (c : Nat) :
  {{ kvStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memCompacted γs c) }}
    (App (Val (s @!! go.GoType.PointerType
      rStorageTy @!! go!"FirstIndex")) (Val #()))
  {{ (fi : w64), RET (PairV #fi #interface.nil);
      ⌜c + 1 ≤ uint.nat fi⌝ ∗ memCompacted γs (uint.nat fi - 1) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs c $$ [HP] as %fi HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem kvStorage.wp_LastIndex (wp : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (e : Nat) :
  {{ kvStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗ memEnd γs e) }}
    (App (Val (s @!! go.GoType.PointerType
      rStorageTy @!! go!"LastIndex")) (Val #()))
  {{ (li : w64), RET (PairV #li #interface.nil); memEnd γs e ∗ ⌜uint.nat li + 1 = e⌝ }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs e  $$ [HP] as %li HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem kvStorage.wp_Term (wp : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) (i0 : w64)
    (ec : GoInterface) :
  {{ kvStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memLog γs k dq es ∗ ⌜k ≤ uint.nat i0 ∧ uint.nat i0 < k + es.length⌝ ∗
      globalAddr ErrCompacted ↦□ ec) }}
    (App (Val (s @!! go.GoType.PointerType
      rStorageTy @!! go!"Term")) (Val #i0))
  {{ (t : w64) (err : GoInterface), RET (PairV #t #err);
      memLog γs k dq es ∗
      (⌜err = interface.nil ∧ (fun e : EntryM => e.Term') <$> es[uint.nat i0 - k]? = some t⌝ ∨
       (⌜err = ec⌝ ∗ memCompacted γs (uint.nat i0 + 1))) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs k dq es i0 ec  $$ [HP] as %t %err HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem kvStorage.wp_Entries (wp : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq1 dq2 : DFrac) (a b : List EntryM)
    (lo hi maxSize : w64) (ec : GoInterface) :
  {{ kvStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memLog γs k dq1 a ∗ memLog γs (k + a.length) dq2 b ∗
      ⌜k ≤ uint.nat lo ∧ uint.nat lo < uint.nat hi ∧ uint.nat hi ≤ k + a.length + b.length⌝ ∗
      globalAddr ErrCompacted ↦□ ec) }}
    (App (App (App (Val (s @!! go.GoType.PointerType
      rStorageTy @!! go!"Entries")) (Val #lo)) (Val #hi)) (Val #maxSize))
  {{ (sl : GoSlice) (es : List EntryM) (err : GoInterface), RET (PairV #sl #err);
      memLog γs k dq1 a ∗ memLog γs (k + a.length) dq2 b ∗
      ((⌜err = ec⌝ ∗ memCompacted γs (uint.nat lo)) ∨
       (⌜err = interface.nil⌝ ∗ entsRO sl es ∗
        ⌜es ≠ [] ∧ sl.cap = sl.len ∧
          es <+: ((a ++ b).drop (uint.nat lo - k)).take (uint.nat hi - uint.nat lo)⌝)) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs k dq1 dq2 a b lo hi maxSize ec  $$ [HP] as %sl %es %err HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem kvStorage.wp_Append (wp : MemoryStorage.Append.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (k : Nat) (old es : List EntryM) (sl : GoSlice) (dq : DFrac)
    (h1 : ∀ (j : Nat) (e : EntryM), es[j]? = some e → uint.nat e.Index' = k + j)
    (h2 : k + es.length ≤ 2^61) :
  {{ kvStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) old ∗ memEnd γs (k + old.length)) ∗
      entsPts sl dq es) }}
    (App (Val (s @!! go.GoType.PointerType
      rStorageTy @!! go!"Append")) (Val #sl))
  {{ RET #interface.nil; entsPts sl dq es ∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length)) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs k old es sl dq h1 h2 $$ [HP] as  HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem kvStorage.wp_ApplySnapshot (wp : MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (J : MemJust GF) (j : Nat) (old : List EntryM) (sp : Loc)
    (dq : DFrac) (sv : SnapshotM) (eood : GoInterface)
    (h1 : j ≤ uint.nat sv.Metadata'.Index')
    (h2 : uint.nat sv.Metadata'.Index' < 2^61) :
  {{ kvStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorInvP ms γs J ∗
      memLog γs j (DFrac.own 1) old ∗ memEnd γs (j + old.length) ∗
      J.B (uint.nat sv.Metadata'.Index') ∗ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index') ∗
      snapArg sp dq sv ∗ memSnapLb γs 0 ∗ globalAddr ErrSnapOutOfDate ↦□ eood) }}
    (App (Val (s @!! go.GoType.PointerType
      rStorageTy @!! go!"ApplySnapshot")) (Val #sp))
  {{ RET #interface.nil; ownSnapM sp dq sv ∗
      memCompacted γs (uint.nat sv.Metadata'.Index') ∗
      memLog γs (uint.nat sv.Metadata'.Index') DFrac.discard [memDummy sv] ∗
      memEnd γs (uint.nat sv.Metadata'.Index' + 1) ∗ memSnapLb γs (uint.nat sv.Metadata'.Index') }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs J j old sp dq sv eood h1 h2 $$ [HP] as  HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem kvStorage.wp_SetHardState (wp : MemoryStorage.SetHardState.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (hs : HardStateM) (st : Loc) (hs' : HardStateM) :
  {{ kvStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      memStorMeta ms γs hs ∗ hsOpt st hs') }}
    (App (Val (s @!! go.GoType.PointerType
      rStorageTy @!! go!"SetHardState")) (Val #st))
  {{ RET #interface.nil; memStorMeta ms γs hs' }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs hs st hs'  $$ [HP] as  HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem kvStorage.wp_CreateSnapshot (wp : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (J : MemJust GF) (i : w64) (e : EntryM) (cs : Loc)
    (dq : DFrac) (c : ConfStateM) (data : GoSlice) (bs : List w8) (eood : GoInterface) :
  {{ kvStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorInvP ms γs J ∗
      memLog γs (uint.nat i) DFrac.discard [e] ∗
      J.SV (memSnapMade i e.Term' c bs) ∗ J.DL (uint.nat i) ∗
      memSnapLb γs 0 ∗ ownCSM cs dq c ∗ data ↦* bs ∗
      globalAddr ErrSnapOutOfDate ↦□ eood) }}
    (App (App (App (Val (s @!! go.GoType.PointerType
      rStorageTy @!! go!"CreateSnapshot")) (Val #i)) (Val #cs)) (Val #data))
  {{ (snap : Loc) (err : GoInterface), RET (PairV #snap #err);
      ownCSM cs dq c ∗ memSnapLb γs (uint.nat i) ∗
      ((⌜err = interface.nil⌝ ∗ ownSnapM snap (DFrac.own 1) (memSnapMade i e.Term' c bs)) ∨
       (⌜snap = null ∧ err = eood⌝ ∗ data ↦* bs)) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvStorRec at Hrec
  icases Hrec with ⟨#Hf, -⟩
  try wp_auto
  wp_apply wp ms γs J i e cs dq c data bs eood  $$ [HP] as %snap %err HQ
  · iexact HP
  iapply HΦ
  iexact HQ

theorem kvStorage.wp_Compact (wp : MemoryStorage.Compact.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (J : MemJust GF) (x : w64) (ecomp : GoInterface) :
  {{ kvStorRec (GF := GF) s ms γs ∗
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorInvP ms γs J ∗
      ((∃ (e : EntryM), memLog γs (uint.nat x) DFrac.discard [e]) ∨ memCompacted γs (uint.nat x)) ∗
      J.B (uint.nat x) ∗ memSnapLb γs (uint.nat x) ∗ globalAddr ErrCompacted ↦□ ecomp) }}
    (App (Val (s @!! go.GoType.PointerType
      rStorageTy @!! go!"Compact")) (Val #x))
  {{ (err : GoInterface), RET #err;
      ⌜err = interface.nil ∨ err = ecomp⌝ ∗ memCompacted γs (uint.nat x) }} := by
  wp_start as ⟨#Hrec, HP⟩
  iunfold kvStorRec at Hrec
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- `kvJ`'s compaction justification is the API's (`storBnd`). -/
theorem kvJ_bnd (γ : Cluster) (id : w64) (c : Nat) :
    memBnd (kvJ (GF := GF) γ id) c ⊢ storBnd γ id c := by
  unfold memBnd storBnd kvJ; exact .rfl

theorem kvJ_B0 (γ : Cluster) (id : w64) : ⊢ (kvJ (GF := GF) γ id).B 0 := by
  unfold kvJ
  iintro
  ileft; iapply nodeAppliedLb_zero

/-- **The store's storage meets node `id`'s storage contract** (under `kvStorageModel`). -/
theorem kvStorage_isStorage
    (wp_Snapshot : kv.Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (γ : Cluster) (id : w64) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv -∗
      kvStorRec s ms γs -∗ memStorInvP ms γs (kvJ γ id) -∗
      isStorage γ id (kvStorIface s) := by
  iintro #Hpkg #Hrec #Hinv
  ihave #Hl : memStorLock ms γs $$ []
  · iunfold memStorInvP at Hinv; icases Hinv with ⟨#Hl, -⟩; iexact Hl
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  unfold isStorage isStorageP
  iexists (interface.mk (go.GoType.PointerType
    rStorageTy) #s)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %e
    imodintro
    iintro %Φ He HΦ
    ihave He := kvStorEnd_to s ms γs e $$ Hrec He
    wp_apply kvStorage.wp_LastIndex wp_LastIndex s ms γs e $$ [$Hrec $Hinit $Hl $He] as %li ⟨He, %Hli⟩
    iapply HΦ
    ihave He := kvStorEnd_of s ms γs e $$ Hrec He
    iframe He
    ipureintro; exact Hli
  isplitr
  · iintro %k %dq %es %i0 %ec
    imodintro
    iintro %Φ ⟨H, %Hr, #Hec⟩ HΦ
    ihave H := kvStorLog_to s ms γs k dq es $$ Hrec H
    wp_apply kvStorage.wp_Term wp_Term s ms γs k dq es i0 ec $$ [$Hrec $Hinit $Hl $H $Hec]
      as %t %err ⟨H, Ht⟩
    · ipureintro; exact Hr
    iapply HΦ
    ihave H := kvStorLog_of s ms γs k dq es $$ Hrec H
    iframe H
    icases Ht with (%Ht | ⟨%Ht, #Hc⟩)
    · ileft; ipureintro; exact Ht
    · iright
      isplitr
      · ipureintro; exact Ht
      iapply kvStorCompacted_of s ms γs _ $$ Hrec Hc
  isplitr
  · iintro %k %dq1 %dq2 %a %b %lo %hi %maxSize %ec
    imodintro
    iintro %Φ ⟨Ha, Hb, %Hr, #Hec⟩ HΦ
    ihave Ha := kvStorLog_to s ms γs k dq1 a $$ Hrec Ha
    ihave Hb := kvStorLog_to s ms γs (k + a.length) dq2 b $$ Hrec Hb
    wp_apply kvStorage.wp_Entries wp_Entries s ms γs k dq1 dq2 a b lo hi maxSize ec
      $$ [$Hrec $Hinit $Hl $Ha $Hb $Hec] as %sl %es %err ⟨Ha, Hb, Hres⟩
    · ipureintro; exact Hr
    iapply HΦ $$ %sl %es %err
    ihave Ha := kvStorLog_of s ms γs k dq1 a $$ Hrec Ha
    ihave Hb := kvStorLog_of s ms γs (k + a.length) dq2 b $$ Hrec Hb
    iframe Ha Hb
    icases Hres with (⟨%He, #Hc⟩ | Hres)
    · ileft
      isplitr
      · ipureintro; exact He
      iapply kvStorCompacted_of s ms γs _ $$ Hrec Hc
    · iright; iexact Hres
  isplitr
  · iintro %c
    imodintro
    iintro %Φ #Hc HΦ
    ihave #Hc := kvStorCompacted_to s ms γs c $$ Hrec Hc
    wp_apply kvStorage.wp_FirstIndex wp_FirstIndex s ms γs c $$ [$Hrec $Hinit $Hl $Hc]
      as %fi ⟨%Hfi, #Hc'⟩
    iapply HΦ
    isplitr
    · ipureintro; exact Hfi
    iapply kvStorCompacted_of s ms γs _ $$ Hrec Hc'
  isplitr
  · iintro %c %esu
    imodintro
    iintro %Φ ⟨#Hc, #Hesu⟩ HΦ
    ihave #Hc := kvStorCompacted_to s ms γs c $$ Hrec Hc
    wp_apply wp_Snapshot s ms γs (kvJ γ id) c esu $$ [$Hpkg $Hrec $Hinv $Hc $Hesu]
      as %snap %err Hres
    iapply HΦ
    iexact Hres
  isplitr
  · iintro !> %c #Hc
    ihave #Hc := kvStorCompacted_to s ms γs c $$ Hrec Hc
    imod memCompacted_bound ms γs (kvJ γ id) c $$ Hinv Hc with Hb
    imodintro
    iapply kvJ_bnd γ id c $$ Hb
  iintro !> %k %dq %es H
  ihave H := kvStorLog_to s ms γs k dq es $$ Hrec H
  iunfold memLog at H
  icases H with ⟨H, %Hb⟩
  isplitr
  · ipureintro; exact Hb
  iapply kvStorLog_of s ms γs k dq es $$ Hrec
  iunfold memLog
  iframe H
  ipureintro; exact Hb

/-- **The store's storage before `RestartNode`** (`RestartNode`'s `bootStorage` premise), from what
`NewMemoryStorage` gave of its `MemoryStorage` and the wrapper's records: `FirstIndex` is `1` (the
storage is fresh, `memStorFresh_compacted`), `LastIndex` `0`, and `InitialState` (kv's own: no
`MemoryStorage` call) gives the empty hard state, the voters' conf state, and (allocating the
storage's invariant from `memStorLock ∗ memStorFresh`) the contract. The frame `Q` is the
invariant, which `run` keeps (`runStor`). -/
theorem kvStorage_bootStorage
    (wp_InitialState : kv.Storage.InitialState.spec (GF := GF) (hG := hG))
    (wp_Snapshot : kv.Storage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) (vsl : GoSlice) (voters : List w64)
    (γ : Cluster) (id : w64) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv -∗
      kvStorRec s ms γs -∗ s.[RStorage, go!"voters"] ↦□ vsl -∗ vsl ↦*□ voters -∗
      memStorLock ms γs -∗ memStorFresh ms γs -∗
      memLog γs 0 DFrac.discard [zero_val EntryM] -∗ memEnd γs 1 -∗
      bootStorage γ id (kvStorIface s) (HardStateM.mk (W64 0) (W64 0) (W64 0))
        (kv.kvConfState voters) iprop(memStorInvP ms γs (kvJ γ id)) := by
  iintro #Hpkg #Hrec #Hfield #Hv #Hl Hfresh #Hlog He
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  unfold bootStorage
  iexists (interface.mk (go.GoType.PointerType rStorageTy) #s)
  iexists iprop(memStorFresh ms γs ∗ memEnd γs 1)
  isplitr
  · ipureintro; rfl
  isplitl [Hfresh He]
  · iframe Hfresh He
  isplitr
  · iintro !> %Φ ⟨Hfresh, He⟩ HΦ
    wp_apply kvStorage.wp_FirstIndex wp_FirstIndex s ms γs 0 $$ [$Hrec $Hinit $Hl]
      as %fi ⟨%Hfi, #Hc⟩
    · iapply memCompacted_zero
    icases memStorFresh_compacted ms γs _ $$ [$Hfresh $Hc] with ⟨%H0, Hfresh⟩
    have Hfi1 : fi = W64 1 := by word
    subst Hfi1
    iapply HΦ
    iframe Hfresh He
  isplitr
  · iintro !> %Φ ⟨Hfresh, He⟩ HΦ
    wp_apply kvStorage.wp_LastIndex wp_LastIndex s ms γs 1 $$ [$Hrec $Hinit $Hl $He]
      as %li ⟨He, %Hli⟩
    have Hli0 : li = W64 0 := by word
    subst Hli0
    iapply HΦ
    iframe Hfresh He
  iintro !> %Φ ⟨Hfresh, He⟩ HΦ
  wp_apply wp_InitialState s vsl voters $$ [$Hfield $Hv] as %hp %cs ⟨#Hhs, #Hcs⟩
  iapply HΦ $$ %hp %cs %false
  iframe Hhs Hcs
  imod memStorInvP_alloc ms γs (kvJ γ id) ⊤ $$ Hl Hfresh [] with #Hinv
  · iapply kvJ_B0 γ id
  imodintro
  isplitr
  · iapply kvStorage_isStorage wp_Snapshot wp_LastIndex wp_FirstIndex wp_Term wp_Entries
      s ms γs γ id $$ Hpkg Hrec Hinv
  iframe Hinv
  iexists (zero_val EntryM)
  isplitr
  · ipureintro; rfl
  isplitr
  · iapply kvStorLog_of s ms γs 0 DFrac.discard [zero_val EntryM] $$ Hrec Hlog
  iapply kvStorEnd_of s ms γs 1 $$ Hrec He

end api

end EtcdGrove
end Perennial
