/-
Lean-first (no Rocq counterpart).

# `*kv.Storage` meets raft's `Storage` contract (2026-10-10; raft v3.7, 2026-10-16, stage R6b)

A registered store storage (`kvStorRec s ms γs`) is a raft `Storage` under the
store's storage model (`kvStorageModel`, `Defs.lean`): `isStorage (kvStorIface s)`,
the contract `RestartNode` takes (`kvStorage_isStorage`), and its `InitialState` is what
`newRaft` reads of it (`kvStorage_initialState`). The methods raft calls are the
embedded `MemoryStorage`'s (promoted: the field read, then `MemoryStorage`'s method),
but for `Snapshot` (`Storage.Snapshot`), which says `ErrSnapshotTemporarilyUnavailable`
for the empty snapshot of a new storage: the contract's `Snapshot` clause asked a non-empty
snapshot or that error, which a bare new `MemoryStorage` did not meet until 2026-10-16 (raft
v3.7 stage R8a, D11: the clause now promises a non-empty snapshot only once the storage is
compacted, `prev.index ≠ 0 → Index ≠ 0`, which the store's stronger answer meets
outright). The two laws are `MemoryStorage`'s (`memStorage_handout`, `memStorage_absorb`),
its tokens being of the registered names.

Raft v3.7: the contract's `Entries` hands out read-only entry pointers (`entsRO`) and its
`Snapshot` a fresh owned clone (`ownSnapM`), both `MemoryStorage`'s own results; `InitialState`
returns two fresh pointers, the hard state `hsOpt hp ⟨0, 0, 0⟩` and the conf state of the voters
frozen read-only (`csPts cs □ (kvConfState voters) false`: its `AutoLeave` is `nil`, which
`RestartNode.spec` admits since stage R6b, `al`).

Raft's own instance for a bare `*MemoryStorage` (`memStorageModel`, `memStorage_isStorage`,
`Proof/go_etcd_io/raft/v3/MemstorageInstance.lean`, 2026-10-16, stage R7a: a registry from the
storage's pointer to its names, the snapshot premise `prev.index ≠ 0 → ss.index ≠ 0` in
`ownStorage`) does not serve the store: its `Storage` is its own struct (another interface
value, the promoted methods behind a field read), and its registry is keyed by that struct (its
`MemoryStorage` field holds the registration's exclusivity). (Its `Snapshot` override, which let
it start with no snapshot under the clause before R8a, is no longer needed for that; the
store's Go code is unchanged.) Everything here is store-specific; the method clauses are
proved as raft's are (`is_Storage_MemoryStorage`), one `wp_apply` of `MemoryStorage`'s
collection each.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Storage__Snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Storage__InitialState
public import Proof.go_etcd_io.raft.v3.MemCertLink
public import Proof.go_etcd_io.raft.v3.Linked

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open RaftLink

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section inst
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

include sem in
theorem kvStorIface_inj (s1 s2 : Loc) : kvStorIface s1 = kvStorIface s2 → s1 = s2 := by
  intro h
  simp only [kvStorIface, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    true_and] at h
  exact go.intoVal_inj h

/-- The storage's owner, at a known storage. -/
theorem kvOwnStorage_at (s ms : Loc) (γs : MemStorNames) (σ : StorState) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ ownStorage (kvStorIface s) σ -∗ ownMemoryStorage ms γs σ := by
  iintro #Hrec Hown
  ihave Hown : kvOwnStorage (kvStorIface s) σ $$ [Hown]
  · iexact Hown
  unfold kvOwnStorage
  icases Hown with ⟨%s', %ms', %γs', %Hst, #Hrec', Hown⟩
  have := kvStorIface_inj (GF := GF) _ _ Hst
  subst this
  icases kvStorRec_agree s ms ms' γs γs' $$ Hrec Hrec' with ⟨%H1, %H2⟩
  subst H1 H2
  iexact Hown

theorem kvOwnStorage_intro (s ms : Loc) (γs : MemStorNames) (σ : StorState) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ ownMemoryStorage ms γs σ -∗ ownStorage (kvStorIface s) σ := by
  iintro #Hrec Hown
  ihave H : kvOwnStorage (kvStorIface s) σ $$ [Hown]
  · unfold kvOwnStorage
    iexists s, ms, γs
    iframe Hrec Hown
    ipureintro; rfl
  iexact H

theorem kvStorCut_at (s ms : Loc) (γs : MemStorNames) (n : Int) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ storCut (kvStorIface s) n -∗ memStorCut γs n := by
  iintro #Hrec Hc
  ihave Hc : kvStorCut (kvStorIface s) n $$ [Hc]
  · iexact Hc
  unfold kvStorCut
  icases Hc with ⟨%s', %ms', %γs', %Hst, #Hrec', Hc⟩
  have := kvStorIface_inj (GF := GF) _ _ Hst
  subst this
  icases kvStorRec_agree s ms ms' γs γs' $$ Hrec Hrec' with ⟨%H1, %H2⟩
  subst H1 H2
  iexact Hc

theorem kvStorCut_intro (s ms : Loc) (γs : MemStorNames) (n : Int) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ memStorCut γs n -∗ storCut (kvStorIface s) n := by
  iintro #Hrec Hc
  ihave H : kvStorCut (kvStorIface s) n $$ [Hc]
  · unfold kvStorCut
    iexists s, ms, γs
    iframe Hrec Hc
    ipureintro; rfl
  iexact H

/-- (D22 S-r) The floor's witness, at a known storage: its `MemoryStorage`'s, below `2^61`. -/
theorem kvStorFloor_at (s ms : Loc) (γs : MemStorNames) (x : w64) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ storFloor (kvStorIface s) x -∗
      memFloorTok ms γs x ∗ ⌜uint.Z x < 2 ^ 61⌝ := by
  iintro #Hrec Hc
  ihave Hc : kvStorFloor (kvStorIface s) x $$ [Hc]
  · iexact Hc
  unfold kvStorFloor
  icases Hc with ⟨%s', %ms', %γs', %Hst, #Hrec', Hc, %Hx⟩
  have := kvStorIface_inj (GF := GF) _ _ Hst
  subst this
  icases kvStorRec_agree s ms ms' γs γs' $$ Hrec Hrec' with ⟨%H1, %H2⟩
  subst H1 H2
  iframe Hc
  ipureintro; exact Hx

theorem kvStorCert_at (s ms : Loc) (γs : MemStorNames) (k : SnapTrip) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ storCert (kvStorIface s) k -∗ memStorCert γs k := by
  iintro #Hrec Hc
  ihave Hc : kvStorCert (kvStorIface s) k $$ [Hc]
  · iexact Hc
  unfold kvStorCert
  icases Hc with ⟨%s', %ms', %γs', %Hst, #Hrec', Hc⟩
  have := kvStorIface_inj (GF := GF) _ _ Hst
  subst this
  icases kvStorRec_agree s ms ms' γs γs' $$ Hrec Hrec' with ⟨%H1, %H2⟩
  subst H1 H2
  iexact Hc

theorem kvStorCert_intro (s ms : Loc) (γs : MemStorNames) (k : SnapTrip) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ memStorCert γs k -∗ storCert (kvStorIface s) k := by
  iintro #Hrec Hc
  ihave H : kvStorCert (kvStorIface s) k $$ [Hc]
  · unfold kvStorCert
    iexists s, ms, γs
    iframe Hrec Hc
    ipureintro; rfl
  iexact H

/-- (D22 S-b′3, 2026-10-20) A store storage whose `MemoryStorage`'s registry is tied to `γ`
(`memCertInv`) meets `storCertOk γ`. -/
theorem kvStorCertOk_intro (γ : RaftNames) (s ms : Loc) (γs : MemStorNames) :
    ⊢ memCertInv (GF := GF) γ γs -∗ kvStorRec s ms γs -∗ storCertOk γ (kvStorIface s) := by
  iintro #Hinv #Hrec
  unfold storCertOk
  isplit
  · iintro !> %k %E %hE #Hc
    ihave #Hc := kvStorCert_at s ms γs k $$ Hrec Hc
    iapply memCert_read γ γs k E hE $$ Hinv Hc
  · iintro !> %k %E %hE #Hk
    imod memCert_register γ γs k E hE $$ Hinv Hk with #Hc
    imodintro
    iapply kvStorCert_intro s ms γs k $$ Hrec Hc

/-- **The store's storage is a raft `Storage`.** -/
theorem kvStorage_isStorage
    (wp_Snapshot : kv.Storage.Snapshot.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv -∗
      kvStorRec (GF := GF) s ms γs -∗ isStorage (kvStorIface s) := by
  iintro #Hpkg #Hrec
  ihave #Hrec' := Hrec
  iunfold kvStorRec at Hrec'
  icases Hrec' with ⟨#Hfield, -⟩
  unfold isStorage isStorageWith
  iexists (⟨go.GoType.PointerType rStorageTy, #s⟩ : GoInterfaceOk)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %σ
    imodintro
    iintro %Φ ⟨Hown, %Hpn⟩ HΦ
    ihave Hown := kvOwnStorage_at s ms γs σ $$ Hrec Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_method_call
    wp_auto
    wp_apply MemoryStorage.wp_LastIndex $$ [$Hown] as %li ⟨%Hli, Hown⟩
    · ipureintro; exact Hpn
    iapply HΦ
    ihave Hown := kvOwnStorage_intro s ms γs σ $$ Hrec Hown
    iframe Hown
    ipureintro; exact Hli
  isplitr
  · iintro %σ
    imodintro
    iintro %Φ Hown HΦ
    ihave Hown := kvOwnStorage_at s ms γs σ $$ Hrec Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_method_call
    wp_auto
    wp_apply MemoryStorage.wp_FirstIndex $$ [$Hown] as %fi ⟨%Hfi, #Hcut, Hown⟩
    iapply HΦ
    ihave Hown := kvOwnStorage_intro s ms γs σ $$ Hrec Hown
    iframe Hown
    isplitr
    · ipureintro; exact Hfi
    icases Hcut with (%Hc | #Hc)
    · ileft; ipureintro; exact Hc
    · iright; iapply kvStorCut_intro s ms γs _ $$ Hrec Hc
  isplitr
  · iintro %σ %i0 %ec
    imodintro
    iintro %Φ ⟨Hown, %Hr, %Hpf, #Hec⟩ HΦ
    ihave Hown := kvOwnStorage_at s ms γs σ $$ Hrec Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_method_call
    wp_auto
    wp_apply MemoryStorage.wp_Term ms γs σ i0 ec $$ [$Hown $Hec] as %t %err ⟨Ht, Hown⟩
    · ipureintro; exact ⟨Hr, Hpf⟩
    iapply HΦ
    ihave Hown := kvOwnStorage_intro s ms γs σ $$ Hrec Hown
    iframe Hown
    icases Ht with (%Ht | ⟨%Ht, #Hc⟩)
    · ileft; ipureintro; exact Ht
    · iright
      isplitr
      · ipureintro; exact Ht
      iapply kvStorCut_intro s ms γs _ $$ Hrec Hc
  isplitr
  · iintro %σ %lo %hi %maxSize %ec
    imodintro
    iintro %Φ ⟨Hown, %Hr, %Hpf, #Hec⟩ HΦ
    ihave Hown := kvOwnStorage_at s ms γs σ $$ Hrec Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_method_call
    wp_auto
    wp_apply MemoryStorage.wp_Entries ms γs σ lo hi maxSize ec $$ [$Hown $Hec]
      as %sl %es %err Hres
    · ipureintro; exact ⟨Hr, Hpf⟩
    iapply HΦ $$ %sl %es %err
    icases Hres with (⟨%He, #Hc, Hown⟩ | ⟨%He, Hs, %Hp, Hown⟩)
    · ileft
      ihave Hown := kvOwnStorage_intro s ms γs σ $$ Hrec Hown
      iframe Hown
      isplitr
      · ipureintro; exact He
      iapply kvStorCut_intro s ms γs _ $$ Hrec Hc
    · iright
      ihave Hown := kvOwnStorage_intro s ms γs σ $$ Hrec Hown
      iframe Hown Hs
      ipureintro; exact ⟨He, Hp⟩
  isplitr
  · imodintro
    iintro %σ Hown
    ihave Hown := kvOwnStorage_at s ms γs σ $$ Hrec Hown
    icases ownMemoryStorage_bounded ms γs σ $$ Hown with ⟨%Hb, Hown⟩
    ihave Hown := kvOwnStorage_intro s ms γs σ $$ Hrec Hown
    iframe Hown
    ipureintro; exact Hb
  isplitr
  · iintro %σ %esu %n
    imodintro
    iintro %Φ ⟨Hown, #Hesu, #Hn⟩ HΦ
    ihave Hown := kvOwnStorage_at s ms γs σ $$ Hrec Hown
    ihave #Hn' : (⌜n ≤ 0⌝ ∨ memStorCut (GF := GF) γs n) $$ []
    · icases Hn with (%Hc | #Hc)
      · ileft; ipureintro; exact Hc
      · iright; iapply kvStorCut_at s ms γs _ $$ Hrec Hc
    wp_apply wp_Snapshot s ms γs σ esu n $$ [$Hfield $Hown $Hesu $Hn'] as %snap %err ⟨Hown, Hr⟩
    iapply HΦ
    ihave Hown := kvOwnStorage_intro s ms γs σ $$ Hrec Hown
    iframe Hown
    -- the store's answer is non-empty outright; the clause asks it only once compacted
    icases Hr with (%Herr | ⟨%Herr, %sv, Hv, %Hsv, #Hc⟩)
    · ileft; ipureintro; exact Herr
    iright
    isplitr
    · ipureintro; exact Herr
    iexists sv
    iframe Hv
    isplitr
    · ipureintro
      exact ⟨fun _ => Hsv.1, Hsv.2⟩
    iright; iapply kvStorCert_intro s ms γs _ $$ Hrec Hc
  isplitr
  · imodintro
    iintro %σ %p Hown %Hpo
    ihave Hown := kvOwnStorage_at s ms γs σ $$ Hrec Hown
    imod memStorage_handout ms γs σ p Hpo $$ Hown with ⟨Hown, Htok⟩
    ihave Hown := kvOwnStorage_intro s ms γs _ $$ Hrec Hown
    imodintro
    iframe Hown
    ihave H : kvAppendTok (kvStorIface s) σ p $$ [Htok]
    · unfold kvAppendTok
      iexists s, ms, γs
      iframe Hrec Htok
      ipureintro; rfl
    iexact H
  isplitr
  imodintro
  iintro %σ1 %σ %p Hown Ht
  ihave Hown := kvOwnStorage_at s ms γs σ1 $$ Hrec Hown
  ihave Ht : kvAppendedTok (kvStorIface s) σ p $$ [Ht]
  · iexact Ht
  unfold kvAppendedTok
  icases Ht with ⟨%s', %ms', %γs', %Hst, #Hrec2, Ht⟩
  have := kvStorIface_inj (GF := GF) _ _ Hst
  subst this
  icases kvStorRec_agree s ms ms' γs γs' $$ Hrec Hrec2 with ⟨%H1, %H2⟩
  subst H1 H2
  imod memStorage_absorb ms γs σ1 σ p $$ Hown Ht with ⟨%Heq, Hown⟩
  ihave Hown := kvOwnStorage_intro s ms γs _ $$ Hrec Hown
  imodintro
  iframe Hown
  ipureintro; exact Heq
  imodintro
  iintro %σ %x Hown %Hx
  ihave Hown := kvOwnStorage_at s ms γs σ $$ Hrec Hown
  icases ownMemoryStorage_bounded ms γs σ $$ Hown with ⟨%Hb, Hown⟩
  imod memStorage_floor ms γs σ x Hx $$ Hown with ⟨Hown, Hfw⟩
  ihave Hown := kvOwnStorage_intro s ms γs _ $$ Hrec Hown
  ihave H : kvStorFloor (kvStorIface s) x $$ [Hfw]
  · unfold kvStorFloor
    iexists s, ms, γs
    iframe Hrec Hfw
    ipureintro; exact ⟨rfl, by have := Hx.2.2; omega⟩
  imodintro
  iframe Hown H

/-- `InitialState`, as `RestartNode` asks of its storage (`RestartNode.spec`'s premise, the shape
of `newRaft`'s): a fresh empty hard state (`hsOpt`) and the voters' conf state, read-only for
good, its `AutoLeave` cell unset (`al = false`: the store sets none; 2026-10-16, stage R6b,
raft's specs admit either), the owner's state unchanged. -/
theorem kvStorage_initialState
    (wp_InitialState : kv.Storage.InitialState.spec (GF := GF) (hG := hG))
    (s : Loc) (vsl : GoSlice) (voters : List w64) (σ : StorState) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv -∗
      s.[RStorage, go!"voters"] ↦□ vsl -∗ vsl ↦*□ voters -∗
      □ (∀ (Φ : val → IProp GF) (ss' : entryID),
           ownStorage (kvStorIface s) { σ with ss := ss' } -∗
           (∀ (hp cs : Loc) (al : Bool), ownStorage (kvStorIface s) { σ with ss := ss' } -∗
            hsOpt hp (HardStateM.mk (W64 0) (W64 0) (W64 0)) -∗
            csPts cs DFrac.discard (kv.kvConfState voters) al -∗
            Φ (PairV (PairV #hp #cs) #interface.nil)) -∗
           WP (App (Val #(methods (go.GoType.PointerType rStorageTy) go!"InitialState" #s))
             (Val #())) {{ Φ }}) := by
  iintro #Hpkg #Hfield #Hv
  imodintro
  iintro %Φ %ss' Hown HΦ
  wp_apply wp_InitialState s vsl voters $$ [$Hfield $Hv] as %hp %cs ⟨#Hhs, #Hcs⟩
  iapply HΦ $$ %hp %cs %false Hown Hhs Hcs

end inst

end EtcdGrove
end Perennial
