/-
Shared definitions, contracts, and lemmas for `bootstrappedWAL` and `bootstrapWALFromSnapshot`
(`server/v3/etcdserver/bootstrap.go:600-804`, PR `etcd-io/etcd#22655`). Lean-first.

### Overview

`bootstrapWALFromSnapshot` opens a WAL from `snapshot`, optionally truncates uncommitted entries
and fills any backend-ahead gap with empty `EntryNormal` entries when `cfg.ForceNewCluster` is set
(PR #22655's `fillBackendAheadGap`), appends single-node configuration-change entries
(`NewConfigChangeEntries` + `AppendAndCommitEntries`), and returns a `*bootstrappedWAL` whose
`MemoryStorage()` method populates a `raft.MemoryStorage` via `NewMemoryStorage`, `ApplySnapshot`,
`SetHardState`, and `Append`.

Because `bootstrapWALFromSnapshot` and `AppendAndCommitEntries` mutate `wal.st.Commit` in place
(`bwal.st.Commit = new(max(oldCommitIndex, consistentIndex))` at line 624 and
`wal.st.Commit = wal.ents[len(wal.ents)-1].Index` at line 802), a `*bootstrappedWAL`'s
`st : *raftpb.HardState` is owned (`hsPts p (DFrac.own 1) hs`) during bootstrap and frozen to
`hsRO p hs` (`hsPts_persist`) when passed to `MemoryStorage.SetHardState`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvNodeStart
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.EntryType__Enum
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.NewMemoryStorage
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Fatal
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.Int
public import Spec.go_uber_org.zap.Error

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage go_etcd_io.etcd.server.v3.storage.wal
  go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.raft.v3 go_uber_org

section typeRepr
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

instance (priority := high) bootstrappedWAL_typeRepr : TypeRepr bootstrappedWAL.ty bootstrappedWAL :=
  go.type_repr_underlying (u := bootstrappedWAL.underlying)
instance (priority := high) bootstrappedWAL_typeRepr_u :
    TypeRepr bootstrappedWAL.underlying bootstrappedWAL :=
  go.type_repr_underlying (u := bootstrappedWAL.underlying)
instance (priority := high) snapshotMetadata_typeRepr :
    TypeRepr snapshotMetadata.ty snapshotMetadata :=
  go.type_repr_underlying (u := snapshotMetadata.underlying)
instance (priority := high) snapshotMetadata_typeRepr_u :
    TypeRepr snapshotMetadata.underlying snapshotMetadata :=
  go.type_repr_underlying (u := snapshotMetadata.underlying)

end typeRepr

/-! ## Pure model of WAL entries and gap filling -/

section pure
variable [FfiSyntax]

/-- The zero `SnapshotM`, corresponding to `wal.snapshot == nil` (`memStorApplied snapZero =
memStorEmpty`). -/
def snapZero : SnapshotM :=
  SnapshotM.mk [] (SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false) (W64 0) (W64 0))

@[simp]
theorem memStorApplied_snapZero : memStorApplied snapZero = memStorEmpty := rfl

/-- The last WAL index as computed by `fillBackendAheadGap` (`bootstrap.go:766-771`):
the last entry's `Index` if `es` is non-empty, else the snapshot's metadata `Index`. -/
def walLastIndex (sv : SnapshotM) (es : List EntryM) : w64 :=
  match es.getLast? with
  | some e => e.Index'
  | none => sv.Metadata'.Index'

/-- The `HardState` after `AppendAndCommitEntries` appends `ents` onto `es`: if `es ++ ents` is
non-empty, `Commit'` is updated to the last entry's `Index'`; otherwise `hs` is unchanged. -/
def hsAfterAppend (hs : HardStateM) (es ents : List EntryM) : HardStateM :=
  match (es ++ ents).getLast? with
  | some e => { hs with Commit' := e.Index' }
  | none => hs

/-- A single empty `EntryNormal` entry at `term` and `idx` (`fillBackendAheadGap`,
`bootstrap.go:782-786`). -/
def gapEntry (term idx : w64) : EntryM :=
  { Term' := term, Index' := idx, Type' := W32 0, Data' := [] }

/-- `n` consecutive empty `EntryNormal` entries at `term` starting at `startIdx + 1`. -/
def gapEntriesAux (term startIdx : w64) : Nat → List EntryM
  | 0 => []
  | n + 1 =>
    gapEntriesAux term startIdx n ++ [gapEntry term (W64 (uint.Z startIdx + 1 + (n : Int)))]

/-- The empty `EntryNormal` entries `fillBackendAheadGap` appends between `lastIdx` and `commit`:
`[]` when `commit ≤ lastIdx`, or indices `lastIdx + 1 .. commit` at `term` when `lastIdx < commit`. -/
def gapEntries (term lastIdx commit : w64) : List EntryM :=
  gapEntriesAux term lastIdx (uint.Z commit - uint.Z lastIdx).toNat

@[simp]
theorem gapEntriesAux_zero (term startIdx : w64) :
    gapEntriesAux term startIdx 0 = [] := rfl

theorem gapEntriesAux_succ (term startIdx : w64) (n : Nat) :
    gapEntriesAux term startIdx (n + 1) =
      gapEntriesAux term startIdx n ++ [gapEntry term (W64 (uint.Z startIdx + 1 + (n : Int)))] :=
  rfl

@[simp]
theorem gapEntriesAux_length (term startIdx : w64) (n : Nat) :
    (gapEntriesAux term startIdx n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [gapEntriesAux, ih]

@[simp]
theorem gapEntries_length (term lastIdx commit : w64) :
    (gapEntries term lastIdx commit).length = (uint.Z commit - uint.Z lastIdx).toNat := by
  simp [gapEntries]

theorem gapEntries_of_le (term lastIdx commit : w64) (h : uint.Z commit ≤ uint.Z lastIdx) :
    gapEntries term lastIdx commit = [] := by
  unfold gapEntries
  have h0 : (uint.Z commit - uint.Z lastIdx).toNat = 0 := by omega
  rw [h0]; rfl

theorem gapEntriesAux_getElem? (term startIdx : w64) (n i : Nat) :
    (gapEntriesAux term startIdx n)[i]? =
      if i < n then some (gapEntry term (W64 (uint.Z startIdx + 1 + (i : Int)))) else none := by
  induction n with
  | zero => simp [gapEntriesAux]
  | succ n ih =>
    rw [gapEntriesAux_succ, List.getElem?_append, gapEntriesAux_length, ih]
    by_cases hlt : i < n
    · have hlt' : i < n + 1 := by omega
      simp [hlt, hlt']
    · by_cases heq : i = n
      · subst heq
        simp
      · have h1 : ¬ i < n + 1 := by omega
        have h2 : 1 ≤ i - n := by omega
        have hnone : ([gapEntry term (W64 (uint.Z startIdx + 1 + (n : Int)))])[i - n]? = none :=
          List.getElem?_eq_none (by simpa using h2)
        simp [hlt, h1, hnone]

theorem gapEntries_eq_snoc_of_lt (term lastIdx commit : w64)
    (hlt : uint.Z lastIdx < uint.Z commit) :
    gapEntries term lastIdx commit =
      gapEntriesAux term lastIdx ((uint.Z commit - uint.Z lastIdx).toNat - 1) ++
        [gapEntry term commit] := by
  unfold gapEntries
  generalize hm : (uint.Z commit - uint.Z lastIdx).toNat = m
  cases m with
  | zero => omega
  | succ m' =>
    simp only [Nat.add_sub_cancel, gapEntriesAux_succ]
    congr 3
    have h1 : W64 (uint.Z lastIdx + 1 + (m' : Int)) = commit := by word
    rw [h1]

theorem hsAfterAppend_gapEntries (hs : HardStateM) (es : List EntryM) (lastIdx : w64)
    (hlt : uint.Z lastIdx < uint.Z hs.Commit') :
    hsAfterAppend hs es (gapEntries hs.Term' lastIdx hs.Commit') = hs := by
  unfold hsAfterAppend
  rw [gapEntries_eq_snoc_of_lt _ _ _ hlt, ← List.append_assoc, List.getLast?_concat]
  cases hs; rfl

/-- Under `PlogWf (snapId sv) es`, `walLastIndex sv es` is `sv.Metadata'.Index' + es.length`. -/
theorem walLastIndex_plogWf (sv : SnapshotM) (es : List EntryM)
    (hwf : PlogWf (snapId sv) es) :
    uint.Z (walLastIndex sv es) = uint.Z sv.Metadata'.Index' + (es.length : Int) := by
  unfold walLastIndex
  rw [List.getLast?_eq_getElem?]
  cases hlast : es[es.length - 1]? with
  | none =>
    have hge : es.length ≤ es.length - 1 := List.getElem?_eq_none_iff.1 hlast
    have h0 : es.length = 0 := by omega
    simp [h0]
  | some e =>
    have hlt : es.length - 1 < es.length := (List.getElem?_eq_some_iff.1 hlast).1
    have hidx := hwf (es.length - 1) e hlast
    simp only [snapId] at hidx ⊢
    omega

/-- If `PlogWf b es1` and `es2` has consecutive indices starting at `b.index' + es1.length + 1`,
then `PlogWf b (es1 ++ es2)`. -/
theorem plogWf_append_consecutive (b : entryID) (es1 es2 : List EntryM)
    (hwf1 : PlogWf b es1)
    (hes2 : ∀ (i : Nat) (e : EntryM), es2[i]? = some e →
      uint.Z e.Index' = uint.Z b.index' + (es1.length : Int) + 1 + (i : Int)) :
    PlogWf b (es1 ++ es2) := by
  intro k e hk
  rw [List.getElem?_append] at hk
  split at hk
  · exact hwf1 k e hk
  · rename_i hge
    have hi := hes2 (k - es1.length) e hk
    omega

/-- Appending `gapEntries term (walLastIndex sv es1) commit` preserves `PlogWf (snapId sv)` and
advances `walLastIndex` to `commit`. -/
theorem plogWf_append_gapEntries (sv : SnapshotM) (es1 : List EntryM) (term commit : w64)
    (hwf1 : PlogWf (snapId sv) es1)
    (hle : uint.Z (walLastIndex sv es1) ≤ uint.Z commit) :
    PlogWf (snapId sv) (es1 ++ gapEntries term (walLastIndex sv es1) commit) ∧
      uint.Z (walLastIndex sv (es1 ++ gapEntries term (walLastIndex sv es1) commit)) =
        uint.Z commit := by
  have hlast1 := walLastIndex_plogWf sv es1 hwf1
  have hgap_idx : ∀ (i : Nat) (e : EntryM),
      (gapEntries term (walLastIndex sv es1) commit)[i]? = some e →
      uint.Z e.Index' = uint.Z (snapId sv).index' + (es1.length : Int) + 1 + (i : Int) := by
    intro i e he
    unfold gapEntries at he
    rw [gapEntriesAux_getElem?] at he
    split at he
    · rename_i hlt
      injection he with he
      subst he
      simp only [gapEntry, snapId]
      have hci : uint.Z commit < 2 ^ 64 := by word
      have hpos : 0 ≤ uint.Z sv.Metadata'.Index' := by word
      have hw : uint.Z (W64 (uint.Z (walLastIndex sv es1) + 1 + (i : Int))) =
          uint.Z (walLastIndex sv es1) + 1 + (i : Int) := by word
      omega
    · cases he
  have hwf2 := plogWf_append_consecutive (snapId sv) es1
    (gapEntries term (walLastIndex sv es1) commit) hwf1 hgap_idx
  refine ⟨hwf2, ?_⟩
  rw [walLastIndex_plogWf sv _ hwf2, List.length_append, gapEntries_length]
  omega

/-- For any non-empty `es` satisfying `PlogWf (snapId sv) es`, `PendOk (memStorApplied sv) es` and
`PendAbove (memStorApplied sv) es` hold, and absorbing `es` into `memStorApplied sv` yields
`{ memStorApplied sv with ents := es }`. -/
theorem pendOk_memStorApplied_of_plogWf (sv : SnapshotM) (es : List EntryM)
    (hne : es ≠ []) (hwf : PlogWf (snapId sv) es) :
    PendOk (memStorApplied sv) es ∧
      PendAbove (memStorApplied sv) es ∧
      storAbsorb { memStorApplied sv with pend := es } = { memStorApplied sv with ents := es } := by
  cases es with
  | nil => exact absurd rfl hne
  | cons e0 rest =>
    have he0 := hwf 0 e0 rfl
    simp only [snapId] at he0
    have hpos : 0 ≤ uint.Z sv.Metadata'.Index' := by word
    have hfl : uint.Z (memStorApplied sv).fl = 0 := rfl
    refine ⟨⟨by simp, fun e he => ?_⟩, fun e he => ?_, ?_⟩
    · injection he with he; subst he
      simp only [memStorApplied, snapId, List.length_nil]
      refine ⟨by omega, by omega, fun k ek hek => ?_⟩
      have hk := hwf k ek hek
      simp only [snapId] at hk
      omega
    · injection he with he; subst he
      rw [hfl]
      omega
    · unfold storAbsorb storApp
      simp [memStorApplied]

end pure

/-! ## Heap predicates and lemmas for `bootstrappedWAL` -/

section heap
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A `*raftpb.Snapshot` pointer `p` in `bootstrappedWAL`: either `null` with `sv = snapZero`, or
read-only with every pointer field set (`ownSnapS p DFrac.discard sv`). -/
def snapOptRO (p : Loc) (sv : SnapshotM) : IProp GF :=
  iprop(⌜p = null ∧ sv = snapZero⌝ ∨ ownSnapS p DFrac.discard sv)

instance snapOptRO_persistent (p : Loc) (sv : SnapshotM) :
    Persistent (snapOptRO (GF := GF) p sv) := by
  unfold snapOptRO; infer_instance

/-- A `*raftpb.HardState` at `p` holding `hs`, with its pointer fields owned at `dq`
(`bootstrapWALFromSnapshot` and `AppendAndCommitEntries` overwrite `p.Commit` in place before
`MemoryStorage` freezes the struct to `hsRO p hs`). -/
def hsPts (p : Loc) (dq : DFrac) (hs : HardStateM) : IProp GF :=
  iprop(∃ (pt pv pc : Loc) (uf : List w8),
    "%Hnn" ∷ ⌜p ≠ null⌝ ∗
    "HT" ∷ p.[raftpb.HardState, go!"Term"] ↦{dq} pt ∗ "#cT" ∷ cellRO pt hs.Term' ∗
    "HV" ∷ p.[raftpb.HardState, go!"Vote"] ↦{dq} pv ∗ "#cV" ∷ cellRO pv hs.Vote' ∗
    "HC" ∷ p.[raftpb.HardState, go!"Commit"] ↦{dq} pc ∗ "#cC" ∷ cellRO pc hs.Commit' ∗
    "#Hpb" ∷ pbMsg raftpb.HardState p uf)

/-- Freezing `hsPts p dq hs` yields raft's read-only `hsRO p hs`. -/
theorem hsPts_persist (p : Loc) (dq : DFrac) (hs : HardStateM) :
    hsPts (GF := GF) p dq hs ⊢ |==> hsRO p hs := by
  iintro H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ pt).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ pv).dfractional_persist _ $$ HV with #HV
  imod (typedPointsto_dfractional (GF := GF) _ pc).dfractional_persist _ $$ HC with #HC
  imodintro
  iunfold hsRO
  iexists pt, pv, pc, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HT cT HV cV HC cC Hpb

theorem hsPts_not_null (p : Loc) (dq : DFrac) (hs : HardStateM) :
    hsPts (GF := GF) p dq hs ⊢ ⌜p ≠ null⌝ ∗ hsPts p dq hs := by
  iintro H
  iNamed H
  isplitr
  · ipureintro; exact Hnn
  iunfold hsPts
  iexists pt, pv, pc, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HT cT HV cV HC cC Hpb

/-- Overwriting `p.Commit` with a cell `pc'` holding `c'` updates `hsPts p (DFrac.own 1) hs` to
`{ hs with Commit' := c' }`. -/
theorem hsPts_Commit_acc (p : Loc) (hs : HardStateM) :
    hsPts (GF := GF) p (DFrac.own 1) hs ⊢
      ∃ pc : Loc, p.[raftpb.HardState, go!"Commit"] ↦ pc ∗
        (∀ (pc' : Loc) (c' : w64),
          p.[raftpb.HardState, go!"Commit"] ↦ pc' -∗ cellRO pc' c' -∗
            hsPts p (DFrac.own 1) { hs with Commit' := c' }) := by
  iintro H
  iNamed H
  iexists pc
  iframe HC
  iintro %pc' %c' HC #cC'
  iunfold hsPts
  iexists pt, pv, pc', uf
  isplitr
  · ipureintro; exact Hnn
  iframe HT cT HV cV HC cC' Hpb

/-- Extracting `Index` pointer `pi` and its `cellRO pi e.Index'` from `entRO l e` (used by
`AppendAndCommitEntries`'s `wal.st.Commit = wal.ents[len(wal.ents)-1].Index`). -/
theorem entRO_Index_acc (l : Loc) (e : EntryM) :
    entRO (GF := GF) l e ⊢
      ∃ pi : Loc, l.[raftpb.Entry, go!"Index"] ↦□ pi ∗ cellRO pi e.Index' := by
  iintro H
  iNamed H
  iexists pi
  iframe HI cI

/-- `(*HardState).GetCommit()` on a mutable `hsPts p dq hs`. -/
theorem wp_hsPts_GetCommit (p : Loc) (dq : DFrac) (hs : HardStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hsPts p dq hs }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetCommit"))
        (Val #()))
    {{ RET #hs.Commit'; hsPts p dq hs }} := by
  wp_start as Hh
  iNamed Hh
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  ihave (⟨%Hq, %Hv⟩ | ⟨#Hq, %Hqn⟩) := cellRO_cases $$ cC
  · subst Hq
    wp_auto
    rw [show (W64 0) = hs.Commit' from Hv.symm]
    iapply HΦ
    iunfold hsPts
    iexists pt, pv, null, uf
    isplitr
    · ipureintro; exact Hnn
    iframe HT cT HV cV HC cC Hpb
  · wp_if_destruct
    · exact absurd rfl Hqn
    · iapply HΦ
      iunfold hsPts
      iexists pt, pv, pc, uf
      isplitr
      · ipureintro; exact Hnn
      iframe HT cT HV cV HC cC Hpb

/-- `(*HardState).GetTerm()` on a mutable `hsPts p dq hs`. -/
theorem wp_hsPts_GetTerm (p : Loc) (dq : DFrac) (hs : HardStateM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ hsPts p dq hs }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetTerm"))
        (Val #()))
    {{ RET #hs.Term'; hsPts p dq hs }} := by
  wp_start as Hh
  iNamed Hh
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  ihave (⟨%Hq, %Hv⟩ | ⟨#Hq, %Hqn⟩) := cellRO_cases $$ cT
  · subst Hq
    wp_auto
    rw [show (W64 0) = hs.Term' from Hv.symm]
    iapply HΦ
    iunfold hsPts
    iexists null, pv, pc, uf
    isplitr
    · ipureintro; exact Hnn
    iframe HT cT HV cV HC cC Hpb
  · wp_if_destruct
    · exact absurd rfl Hqn
    · iapply HΦ
      iunfold hsPts
      iexists pt, pv, pc, uf
      isplitr
      · ipureintro; exact Hnn
      iframe HT cT HV cV HC cC Hpb

/-- Appending two entry slices (`wal.ents = append(wal.ents, ents)`). -/
theorem entsPts_append (s' : GoSlice) (ls1 ls2 : List Loc) (es1 es2 : List EntryM) :
    s' ↦* (ls1 ++ ls2) ∗
      ([∗list] l;e ∈ ls1;es1, entRO (GF := GF) l e) ∗
      ([∗list] l;e ∈ ls2;es2, entRO l e) ⊢
      entsPts s' (DFrac.own 1) (es1 ++ es2) := by
  iintro ⟨Hs', #Hb1, #Hb2⟩
  ihave #Hb := entsBig_app ls1 ls2 es1 es2 $$ [$Hb1 $Hb2]
  iunfold entsPts
  iexists (ls1 ++ ls2)
  iframe Hs' Hb

/-! ## Contracts for WAL and `serverstorage` bootstrap helpers -/

/-- Contract for `(*wal.WAL).Save(st, ents)` during `AppendAndCommitEntries` (`wal` is names-only):
saving an empty `HardState` and `ents` to an open WAL `w` succeeds (`err = nil`) and preserves the
entry slice. -/
def bootWalSaveOk (w : Loc) : IProp GF :=
  iprop(□ ∀ (hst : Loc) (s : GoSlice) (dq : DFrac) (es : List EntryM),
    {{ hsRO hst (HardStateM.mk (W64 0) (W64 0) (W64 0)) ∗ entsPts s dq es }}
      (App (App (Val (w @!! go.GoType.PointerType WAL.ty @!! go!"Save")) (Val #hst)) (Val #s))
    {{ RET #interface.nil; entsPts s dq es }})

instance bootWalSaveOk_persistent (w : Loc) : Persistent (bootWalSaveOk (GF := GF) w) := by
  unfold bootWalSaveOk; infer_instance

/-- Contract for `serverstorage.GetEffectiveNodeIDsFromWALEntries(lg, snap, ents)` and
`serverstorage.CreateConfigChangeEnts(lg, nodeIDs, self, term, index)` (`storage/wal.go`,
names-only in `Code/go_etcd_io/etcd/server/v3/storage.lean`):
given a non-nil logger `lg`, snapshot `snap` holding `sv`, and `ents` holding `es`, they return
configuration-change entries `ccEnts` at `term` with consecutive indices starting at `index + 1`. -/
def bootConfChangeEntsOk (sv : SnapshotM) (es : List EntryM) (self : w64)
    (ccEnts : List EntryM) : IProp GF :=
  iprop(∃ nodeIDs : List w64,
    (□ ∀ (lg snap : Loc) (ents : GoSlice) (dq : DFrac),
      {{ ⌜lg ≠ null⌝ ∗ snapOptRO snap sv ∗ entsPts ents dq es }}
        (App (App (App (Val (@! GetEffectiveNodeIDsFromWALEntries)) (Val #lg))
          (Val #snap)) (Val #ents))
      {{ (ns : GoSlice), RET #ns;
          entsPts ents dq es ∗ ns ↦* nodeIDs }}) ∗
    (□ ∀ (lg : Loc) (ns : GoSlice) (term index : w64),
      {{ ⌜lg ≠ null⌝ ∗ ns ↦* nodeIDs }}
        (App (App (App (App (App (Val (@! CreateConfigChangeEnts)) (Val #lg))
          (Val #ns)) (Val #self)) (Val #term)) (Val #index))
      {{ (cs : GoSlice), RET #cs;
          entsPts cs (DFrac.own 1) ccEnts ∗ ownSliceCap Loc cs (DFrac.own 1) ∗
          ⌜(∀ e ∈ ccEnts, e.Term' = term) ∧
            (∀ (i : Nat) (e : EntryM), ccEnts[i]? = some e →
              uint.Z e.Index' = uint.Z index + 1 + (i : Int))⌝ }}))

instance bootConfChangeEntsOk_persistent (sv : SnapshotM) (es : List EntryM) (self : w64)
    (ccEnts : List EntryM) :
    Persistent (bootConfChangeEntsOk (GF := GF) sv es self ccEnts) := by
  unfold bootConfChangeEntsOk; infer_instance

/-- Contract for `openWALFromSnapshot(cfg, snapshot)` (`bootstrap.go:636`): returns `(w, st, ents,
snap, metaPtr)` with `bootWalSaveOk w`, `hsPts st (DFrac.own 1) hs0`, `entsPts ents (DFrac.own 1) es0`
with capacity, `snapOptRO snap sv`, and `metaPtr ↦ mv`. -/
def openWALFromSnapshotOk (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (snapshot : Loc)
    (w st : Loc) (ents : GoSlice) (snap metaPtr : Loc)
    (hs0 : HardStateM) (es0 : List EntryM) (sv : SnapshotM) (mv : snapshotMetadata) : IProp GF :=
  iprop(□ ({{ True }}
    (App (App (Val (@! openWALFromSnapshot)) (Val #cfg)) (Val #snapshot))
    {{ RET (PairV (PairV (PairV (PairV #w #st) #ents) #snap) #metaPtr);
        bootWalSaveOk w ∗
        hsPts st (DFrac.own 1) hs0 ∗
        entsPts ents (DFrac.own 1) es0 ∗ ownSliceCap Loc ents (DFrac.own 1) ∗
        snapOptRO snap sv ∗
        metaPtr ↦ mv }}))

instance openWALFromSnapshotOk_persistent (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (snapshot w st : Loc) (ents : GoSlice) (snap metaPtr : Loc)
    (hs0 : HardStateM) (es0 : List EntryM) (sv : SnapshotM) (mv : snapshotMetadata) :
    Persistent (openWALFromSnapshotOk (GF := GF) cfg snapshot w st ents snap metaPtr hs0 es0 sv mv) := by
  unfold openWALFromSnapshotOk; infer_instance

/-- Contract for `ci.ConsistentIndex()` on a `cindex.ConsistentIndexer` interface value during
`bootstrapWALFromSnapshot` (instantiated by `consistentIndex.ConsistentIndex.spec` via `wp_ci_get`
or a mock `ConsistentIndexer` in unit tests). -/
def ciConsistentIndexOk (ci : ConsistentIndexer) (ciIdx : w64) : IProp GF :=
  iprop(□ ({{ True }}
    (App (match ci with
      | GoInterface.nil => Panic "nil interface"
      | GoInterface.ok i => Val #(methods i.ty go!"ConsistentIndex" i.v)) (Val #()))
    {{ RET #ciIdx; True }}))

instance ciConsistentIndexOk_persistent (ci : ConsistentIndexer) (ciIdx : w64) :
    Persistent (ciConsistentIndexOk (GF := GF) ci ciIdx) := by
  unfold ciConsistentIndexOk; infer_instance

end heap

end EtcdGrove
end Perennial
