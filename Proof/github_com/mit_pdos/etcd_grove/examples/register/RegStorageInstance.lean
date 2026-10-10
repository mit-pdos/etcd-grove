/-
Lean-first (no Rocq counterpart).

# `*register.Storage` meets raft's `Storage` contract (2026-10-10)

A registered register storage (`regStorRec s ms γs`) is a raft `Storage` under the
register's storage model (`regStorageModel`, `Defs.lean`): `isStorage (regStorIface s)`,
the contract `RestartNode` takes (`regStorage_isStorage`), and its `InitialState` is what
`RestartNode` asks of it (`regStorage_initialState`). The methods raft calls are the
embedded `MemoryStorage`'s (promoted: the field read, then `MemoryStorage`'s method),
but for `Snapshot` (`Storage.Snapshot`), which says `ErrSnapshotTemporarilyUnavailable`
for the empty snapshot of a new storage: the contract's `Snapshot` clause (a non-empty
snapshot or that error), which a bare new `MemoryStorage` does not meet. The two laws
are `MemoryStorage`'s (`memStorage_handout`, `memStorage_absorb`), its tokens being of
the registered names.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Storage__Snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Storage__InitialState

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section inst
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

include sem in
theorem regStorIface_inj (s1 s2 : Loc) : regStorIface s1 = regStorIface s2 → s1 = s2 := by
  intro h
  simp only [regStorIface, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    true_and] at h
  exact go.intoVal_inj h

/-- The storage's owner, at a known storage. -/
theorem regOwnStorage_at (s ms : Loc) (γs : MemStorNames) (σ : StorState) :
    ⊢ regStorRec (GF := GF) s ms γs -∗ ownStorage (regStorIface s) σ -∗ ownMemoryStorage ms γs σ := by
  iintro #Hrec Hown
  ihave Hown : regOwnStorage (regStorIface s) σ $$ [Hown]
  · iexact Hown
  unfold regOwnStorage
  icases Hown with ⟨%s', %ms', %γs', %Hst, #Hrec', Hown⟩
  have := regStorIface_inj _ _ Hst
  subst this
  icases regStorRec_agree s ms ms' γs γs' $$ Hrec Hrec' with ⟨%H1, %H2⟩
  subst H1 H2
  iexact Hown

theorem regOwnStorage_intro (s ms : Loc) (γs : MemStorNames) (σ : StorState) :
    ⊢ regStorRec (GF := GF) s ms γs -∗ ownMemoryStorage ms γs σ -∗ ownStorage (regStorIface s) σ := by
  iintro #Hrec Hown
  ihave H : regOwnStorage (regStorIface s) σ $$ [Hown]
  · unfold regOwnStorage
    iexists s, ms, γs
    iframe Hrec Hown
    ipureintro; rfl
  iexact H

/-- **The register's storage is a raft `Storage`.** -/
theorem regStorage_isStorage
    (wp_Snapshot : register.Storage.Snapshot.spec (GF := GF) (hG := hG))
    (s ms : Loc) (γs : MemStorNames) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register -∗
      regStorRec (GF := GF) s ms γs -∗ isStorage (regStorIface s) := by
  iintro #Hpkg #Hrec
  ihave #Hrec' := Hrec
  iunfold regStorRec at Hrec'
  icases Hrec' with ⟨#Hfield, -⟩
  unfold isStorage isStorageWith
  iexists (⟨go.GoType.PointerType rStorageTy, #s⟩ : GoInterfaceOk)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %σ
    imodintro
    iintro %Φ ⟨Hown, %Hpn⟩ HΦ
    ihave Hown := regOwnStorage_at s ms γs σ $$ Hrec Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_method_call
    wp_auto
    wp_apply MemoryStorage.wp_LastIndex $$ [$Hown] as %li ⟨%Hli, Hown⟩
    · ipureintro; exact Hpn
    iapply HΦ
    ihave Hown := regOwnStorage_intro s ms γs σ $$ Hrec Hown
    iframe Hown
    ipureintro; exact Hli
  isplitr
  · iintro %σ
    imodintro
    iintro %Φ Hown HΦ
    ihave Hown := regOwnStorage_at s ms γs σ $$ Hrec Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_method_call
    wp_auto
    wp_apply MemoryStorage.wp_FirstIndex $$ [$Hown] as %fi ⟨%Hfi, Hown⟩
    iapply HΦ
    ihave Hown := regOwnStorage_intro s ms γs σ $$ Hrec Hown
    iframe Hown
    ipureintro; exact Hfi
  isplitr
  · iintro %σ %i0
    imodintro
    iintro %Φ ⟨Hown, %Hr, %Hpf⟩ HΦ
    ihave Hown := regOwnStorage_at s ms γs σ $$ Hrec Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_method_call
    wp_auto
    wp_apply MemoryStorage.wp_Term $$ [$Hown] as %t ⟨%Ht, Hown⟩
    · ipureintro; exact ⟨Hr, Hpf⟩
    iapply HΦ
    ihave Hown := regOwnStorage_intro s ms γs σ $$ Hrec Hown
    iframe Hown
    ipureintro; exact Ht
  isplitr
  · iintro %σ %lo %hi %maxSize
    imodintro
    iintro %Φ ⟨Hown, %Hr, %Hpf⟩ HΦ
    ihave Hown := regOwnStorage_at s ms γs σ $$ Hrec Hown
    ihave ⟨#Hinit, Hown⟩ := ownMemoryStorage_init ms γs σ $$ Hown
    wp_method_call
    wp_auto
    wp_apply MemoryStorage.wp_Entries $$ [$Hown] as %sl %es ⟨Hs, %Hp, Hown⟩
    · ipureintro; exact ⟨Hr, Hpf⟩
    iapply HΦ
    ihave Hown := regOwnStorage_intro s ms γs σ $$ Hrec Hown
    iframe Hown Hs
    ipureintro; exact Hp
  isplitr
  · imodintro
    iintro %σ Hown
    ihave Hown := regOwnStorage_at s ms γs σ $$ Hrec Hown
    icases ownMemoryStorage_bounded ms γs σ $$ Hown with ⟨%Hb, Hown⟩
    ihave Hown := regOwnStorage_intro s ms γs σ $$ Hrec Hown
    iframe Hown
    ipureintro; exact Hb
  isplitr
  · iintro %σ %esu
    imodintro
    iintro %Φ ⟨Hown, #Hesu⟩ HΦ
    ihave Hown := regOwnStorage_at s ms γs σ $$ Hrec Hown
    wp_apply wp_Snapshot s ms γs σ esu $$ [$Hfield $Hown $Hesu] as %snap %err ⟨Hown, Hr⟩
    iapply HΦ
    ihave Hown := regOwnStorage_intro s ms γs σ $$ Hrec Hown
    iframe Hown Hr
  isplitr
  · imodintro
    iintro %σ %p Hown %Hpo
    ihave Hown := regOwnStorage_at s ms γs σ $$ Hrec Hown
    imod memStorage_handout ms γs σ p Hpo $$ Hown with ⟨Hown, Htok⟩
    ihave Hown := regOwnStorage_intro s ms γs _ $$ Hrec Hown
    imodintro
    iframe Hown
    ihave H : regAppendTok (regStorIface s) σ p $$ [Htok]
    · unfold regAppendTok
      iexists s, ms, γs
      iframe Hrec Htok
      ipureintro; rfl
    iexact H
  imodintro
  iintro %σ1 %σ %p Hown Ht
  ihave Hown := regOwnStorage_at s ms γs σ1 $$ Hrec Hown
  ihave Ht : regAppendedTok (regStorIface s) σ p $$ [Ht]
  · iexact Ht
  unfold regAppendedTok
  icases Ht with ⟨%s', %ms', %γs', %Hst, #Hrec2, Ht⟩
  have := regStorIface_inj _ _ Hst
  subst this
  icases regStorRec_agree s ms ms' γs γs' $$ Hrec Hrec2 with ⟨%H1, %H2⟩
  subst H1 H2
  imod memStorage_absorb ms γs σ1 σ p $$ Hown Ht with ⟨%Heq, Hown⟩
  ihave Hown := regOwnStorage_intro s ms γs _ $$ Hrec Hown
  imodintro
  iframe Hown
  ipureintro; exact Heq

/-- `InitialState`, as `RestartNode` asks of its storage: the empty hard state and the
voters, read-only, the owner's state unchanged. -/
theorem regStorage_initialState
    (wp_InitialState : register.Storage.InitialState.spec (GF := GF) (hG := hG))
    (s : Loc) (vsl : GoSlice) (voters : List w64) (σ : StorState) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register -∗
      s.[RStorage, go!"voters"] ↦□ vsl -∗ vsl ↦*□ voters -∗
      □ (∀ (Φ : val → IProp GF) (ss' : entryID),
           ownStorage (regStorIface s) { σ with ss := ss' } -∗
           (ownStorage (regStorIface s) { σ with ss := ss' } -∗
            ({ (zero_val raftpb.ConfState) with Voters' := vsl } : raftpb.ConfState).Voters'
              ↦*□ voters -∗
            Φ (PairV (PairV #(zero_val raftpb.HardState)
              #({ (zero_val raftpb.ConfState) with Voters' := vsl } : raftpb.ConfState))
              #interface.nil)) -∗
           WP (App (Val #(methods (go.GoType.PointerType rStorageTy) go!"InitialState" #s))
             (Val #())) {{ Φ }}) := by
  iintro #Hpkg #Hfield #Hv
  imodintro
  iintro %Φ %ss' Hown HΦ
  wp_apply wp_InitialState s vsl $$ [$Hfield]
  iapply HΦ $$ Hown
  iexact Hv

end inst

end EtcdGrove
end Perennial
