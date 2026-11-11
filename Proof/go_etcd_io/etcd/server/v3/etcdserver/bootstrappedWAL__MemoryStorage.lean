/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedWAL__MemoryStorage.lean`. Lean-first
(no Rocq counterpart); restart S3 (2026-11-11), D2 (b).

The storage stays detached throughout (`memStorFresh`, justifications `trivJ` nothing reads), as
kvdurable's `openStorage`: `NewMemoryStorage`; `ApplySnapshot` of the WAL's snapshot (always set,
`snapArg` not `nil`) from the fresh range at `1` (base `≥ 1`: the first triple at `j = 1`; base `0`:
the second, the dummy `NewMemoryStorage` froze at `0` the snapshot's, its term `0`); `SetHardState`
(skipped on `nil`: the hard state already zero); `Append` of the entries at the base `+ 1` (skipped
when there are none).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__MemoryStorage
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- Justifications nothing reads (the storage is detached throughout). -/
private def trivJ : MemJust GF where
  SV _ := iprop(True)
  B _ := iprop(True)
  DL _ := iprop(True)
  SV_pers _ := inferInstance
  B_pers _ := inferInstance
  B_timeless _ := inferInstance
  DL_pers _ := inferInstance

/-- The snapshot at base `0` and term `0` stores `NewMemoryStorage`'s dummy. -/
private theorem walSnapCS_dummy_zero (σ : StorContents) (cs : ConfStateM) (h0 : σ.b = 0)
    (ht : σ.base.term' = W64 0) : memDummy (walSnapCS σ cs) = zero_val EntryM := by
  have hi : σ.base.index' = W64 0 := by
    unfold StorContents.b at h0; apply BitVec.eq_of_toNat_eq; simpa using h0
  simp only [memDummy, walSnapCS, hi, ht]
  rfl

/-- `ApplySnapshot` of the WAL's snapshot on the fresh storage, at any base (the two triples). -/
private theorem wp_ApplySnapshot_fresh
    (wp_ApplySnapshot : MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG))
    (ms : Loc) (γs : MemStorNames) (σ : StorContents) (cs : ConfStateM) (sp : Loc) (sdq : DFrac)
    (eood : GoInterface) (Hb61 : σ.b < 2^61) (H0t : σ.b = 0 → σ.base.term' = W64 0) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStorLock ms γs ∗
      memStorFresh ms γs 0 memSnapEmpty ∗ memEnd γs 1 ∗ memLog γs 0 DFrac.discard [zero_val EntryM] ∗
      snapArg sp sdq (walSnapCS σ cs) ∗ memSnapLb γs 0 ∗ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot")) (Val #sp))
  {{ RET #interface.nil; ownSnapM sp sdq (walSnapCS σ cs) ∗
      memCompacted γs σ.b ∗ memLog γs σ.b DFrac.discard [memDummy (walSnapCS σ cs)] ∗
      memEnd γs (σ.b + 1) ∗ memSnapLb γs σ.b ∗ memStorFresh ms γs σ.b (walSnapCS σ cs) }} := by
  iintro %Φ ⟨#Hinit, #Hlock, Hfresh, Hend, #Hd0, Hsnap, #Hlb0, #Heood⟩ HΦ
  ihave Hend1 : memEnd γs (1 + ([] : List EntryM).length) $$ [Hend]
  · iexact Hend
  by_cases Hb0 : σ.b = 0
  · ihave #Hd0 : memLog γs 0 DFrac.discard [memDummy (walSnapCS σ cs)] $$ []
    · rw [walSnapCS_dummy_zero σ cs Hb0 (H0t Hb0)]; iexact Hd0
    wp_apply wp_ApplySnapshot.2 ms γs trivJ (some (0, memSnapEmpty)) [] sp sdq (walSnapCS σ cs) eood
      (by rw [walSnapCS_index]; exact Hb0) $$ [Hfresh Hend1 Hsnap]
      as ⟨Hsnap, #Hcomp, #Hdum, Hend, #Hslb, Hfresh⟩
    · rw [memStorAt_some]
      iframe Hlock Hfresh Hend1 Hd0 Hlb0 Heood Hsnap
      iapply memLog_nil
    iapply HΦ
    rw [Hb0]
    iframe Hsnap Hcomp Hdum Hend Hslb Hfresh
  · wp_apply wp_ApplySnapshot.1 ms γs trivJ (some (0, memSnapEmpty)) 1 [] sp sdq (walSnapCS σ cs) eood
      (by rw [walSnapCS_index]; omega) (by rw [walSnapCS_index]; exact Hb61) $$ [Hfresh Hend1 Hsnap]
      as ⟨Hsnap, #Hcomp, #Hdum, Hend, #Hslb, Hfresh⟩
    · rw [memStorAt_some]
      iframe Hlock Hfresh Hend1 Hlb0 Heood Hsnap
      iapply memLog_nil
    iapply HΦ
    unfold StorContents.b; rw [Nat.zero_max]
    iframe Hsnap Hcomp Hdum Hend Hslb Hfresh

theorem bootstrappedWAL.MemoryStorage.wp_proof
    (wp_NewMemoryStorage : NewMemoryStorage.spec (GF := GF) (hG := hG))
    (wp_ApplySnapshot : MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG))
    (wp_SetHardState : MemoryStorage.SetHardState.spec (GF := GF) (hG := hG))
    (wp_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG)) :
    bootstrappedWAL.MemoryStorage.spec (GF := GF) (hG := hG) := by
  intro w dq bw σ cs sdq edq Hidx Hlast H0t
  wp_start as ⟨Hw, Hsnap, #Hhs, Hents⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hw with ⟨Hw, %Hwnn⟩
  iStructNamed Hw
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_NewMemoryStorage as %ms %γs ⟨#Hlock, #Hd0, Hend, Hnone, Hmeta, Hfresh⟩
  try wp_auto
  imod memSnapNone_open γs $$ Hnone with #Hlb0
  ihave #Hinit := go_etcd_io.raft.v3.isInitialized_access $$ Hraft
  iunfold go_etcd_io.raft.v3.isInitialized at Hinit
  iNamed Hinit
  iunfold errorsNewVar at ErrSnapOODNew
  icases ErrSnapOODNew with ⟨%eood, #Heood, -⟩
  icases snapArg_not_null $$ Hsnap with ⟨Hsnap, %Hspnn⟩
  have Hb61 : σ.b < 2 ^ 61 := by unfold StorContents.last at Hlast; omega
  rw [decide_eq_false Hspnn]
  try wp_auto
  wp_apply wp_ApplySnapshot_fresh wp_ApplySnapshot ms γs σ cs bw.snapshot' sdq _ Hb61 H0t
    $$ [Hfresh Hend Hsnap] as ⟨Hsnap, #Hcomp, #Hdum, Hend, #Hslb, Hfresh⟩
  · iframe Hlock Hfresh Hend Hd0 Hsnap Hlb0 Heood
  try wp_auto
  -- the hard state (`nil`: already zero)
  wp_join iprop("wal" ∷ wal_ptr ↦ w ∗ "st" ∷ w.[bootstrappedWAL, go!"st"] ↦{dq} bw.st' ∗
      "s" ∷ s_ptr ↦ ms ∗ "Hmeta" ∷ memStorMeta ms γs σ.hs)
    at (if: #!decide (bw.st' = null) then _ else _)
    with [wal st s Hmeta] as ⟨wal, st, s, Hmeta⟩
  · by_cases Hst : bw.st' = null
    · rw [decide_eq_true Hst]
      try wp_auto
      iunfold hsOpt at Hhs
      icases Hhs with (%Hz | #Hro)
      · isplitl []; · ipureintro; rfl
        rw [Hz.2]; iframe wal st s Hmeta
      · iunfold hsRO at Hro
        icases Hro with ⟨%pt, %pv, %pc, %uf, %Hnn, -⟩
        exact absurd Hst Hnn
    · rw [decide_eq_false Hst]
      try wp_auto
      wp_apply wp_SetHardState ms γs _ bw.st' σ.hs $$ [$Hmeta $Hhs] as Hmeta
      try wp_auto
      isplitl []; · ipureintro; rfl
      iframe wal st s Hmeta
  try wp_auto
  -- the entries (none: no `Append`)
  ihave %Hlen := entsPts_len bw.ents' edq σ.ents $$ Hents
  have Hidx1 : ∀ (j : Nat) (e : EntryM), σ.ents[j]? = some e → uint.nat e.Index' = σ.b + 1 + j :=
    Hidx
  have Hb61' : σ.b + 1 + σ.ents.length ≤ 2 ^ 61 := by unfold StorContents.last at Hlast; omega
  wp_join iprop("Hlog" ∷ memLog γs (σ.b + 1) (DFrac.own 1) σ.ents ∗
      "Hend" ∷ memEnd γs (σ.last + 1) ∗ "Hents" ∷ entsPts bw.ents' edq σ.ents ∗
      "s" ∷ s_ptr ↦ ms ∗ "wal" ∷ wal_ptr ↦ w ∗
      "ents" ∷ w.[bootstrappedWAL, go!"ents"] ↦{dq} bw.ents')
    at (if: _ then _ else _)
    with [Hend Hents s wal ents] as ⟨Hlog, Hend, Hents, s, wal, ents⟩
  · wp_if_destruct
    · have He : σ.ents = [] := by
        apply List.eq_nil_of_length_eq_zero; obtain ⟨h1, h2⟩ := Hlen; rw [h1, Hif]; rfl
      try wp_auto
      isplitl []; · ipureintro; first | rfl | trivial
      rw [show σ.last + 1 = σ.b + 1 by unfold StorContents.last; rw [He]; rfl]
      iframe Hend Hents s wal ents
      rw [He]; iapply memLog_nil
    · have Hne : σ.ents ≠ [] := by
        intro h; rw [h, List.length_nil] at Hlen; apply Hif; obtain ⟨h1, h2⟩ := Hlen; word
      ihave HA : (if σ.ents = [] then emp else memLog γs (σ.b + 1) (DFrac.own 1) [] ∗
          memEnd γs (σ.b + 1 + ([] : List EntryM).length)) $$ [Hend]
      · rw [if_neg Hne, List.length_nil, Nat.add_zero]
        iframe Hend
        iapply memLog_nil
      wp_apply wp_Append ms γs (σ.b + 1) [] σ.ents bw.ents' edq Hidx1 Hb61' $$ [HA Hents]
        as ⟨Hents, HA⟩
      · iframe Hlock HA Hents
      rw [if_neg Hne]
      icases HA with ⟨Hlog, Hend⟩
      try wp_auto
      isplitl []; · ipureintro; first | rfl | trivial
      rw [show σ.last + 1 = σ.b + 1 + σ.ents.length by unfold StorContents.last; omega]
      iframe Hlog Hend Hents s wal ents
  try wp_auto
  iapply HΦ
  iframe Hsnap Hents Hlock
  isplitl [lg haveWAL w st ents snapshot meta']
  · iapply typedPointsto_combine _ _ _ Hwnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe lg haveWAL w st ents snapshot meta'
  iunfold memStorRestarted
  iframe Hfresh Hmeta Hcomp Hdum Hslb Hlog Hend

end proof

end EtcdGrove
end Perennial
