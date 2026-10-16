/-
The raftpb predicates of the log layer (raft v3.7 retarget, stage R3: `notes/raft-retarget-plan.md`,
D2 and D4; `notes/decisions.md`, "The log layer over read-only entries: the storage contract of
raft v3.7"), on top of `InvPb.lean`:

* **`entsPts s dq es`**, a `[]*pb.Entry` slice holding the entries `es`: the slice of pointers at
  `dq` (`s ↦*{dq} ls`, `ls : List Loc`, existential) and each pointer a read-only log entry
  (`[∗list] l;e ∈ ls;es, entRO l e`). `entsRO s es` (`dq = □`) is persistent, and replaces the old
  proof's `s ↦*□ es` of a `[]pb.Entry` (gogoproto values) one for one: the unstable suffix, the
  storage's entries, a slice `slice`/`Entries` hands out. The slice-level reasoning (capacities,
  sub-slices, `append`, a message's backing array adopted) is the old one on `List Loc`; the
  entries' facts are persistent, so a sub-slice or a concatenation takes them along.
* **`ownSnapE p dq s`**: a snapshot whose `Metadata` is set (what `EnsureSnapshot` returns:
  `MemoryStorage.CreateSnapshot` writes the metadata's fields in place).
* **`hsOpt p hs`**: a `nil`-or-read-only hard state (`MemoryStorage.hardState`).
* Persistence of the snapshot predicates at `□` and the freezing lemmas (`ownSnapM_persist`): the
  log's pending snapshot is a fresh clone (`unstable.restore`, `log_unstable.go:196`) that nothing
  writes after, held read-only.
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A `[]*pb.Entry` at `s` holding the entries `es`: its pointers at `dq`, each a read-only log
entry (D2). -/
def entsPts (s : GoSlice) (dq : DFrac) (es : List EntryM) : IProp GF :=
  iprop(∃ (ls : List Loc), s ↦*{dq} ls ∗ [∗list] l;e ∈ ls;es, entRO l e)

/-- A read-only `[]*pb.Entry`: persistent (the old proof's `s ↦*□ es`). -/
abbrev entsRO (s : GoSlice) (es : List EntryM) : IProp GF := entsPts s DFrac.discard es

/-- A `*pb.Snapshot` at `p` holding `s` whose `Metadata` is set: what `EnsureSnapshot` returns,
so that `MemoryStorage.CreateSnapshot` may write the metadata's fields in place
(`storage.go:255-261`). `ownSnapE_weaken` forgets that the metadata is set. -/
def ownSnapE (p : Loc) (dq : DFrac) (s : SnapshotM) : IProp GF :=
  iprop(∃ (ds : GoSlice) (pm : Loc) (uf : List w8),
    "%Hnn" ∷ ⌜p ≠ null⌝ ∗
    "HD" ∷ p.[raftpb.Snapshot, go!"Data"] ↦{dq} ds ∗ "Hd" ∷ ds ↦*{dq} s.Data' ∗
    "HM" ∷ p.[raftpb.Snapshot, go!"Metadata"] ↦{dq} pm ∗ "Hm" ∷ smPts pm dq s.Metadata' ∗
    "#Hpb" ∷ pbMsg raftpb.Snapshot p uf)

/-- A hard-state pointer that may be `nil`, read as the zero record: `MemoryStorage`'s
`hardState` before the first `SetHardState` (`NewMemoryStorage` leaves it `nil`; `InitialState`
returns it, "may be nil", `storage.go:52-55`). Persistent. -/
def hsOpt (p : Loc) (hs : HardStateM) : IProp GF :=
  iprop(⌜p = null ∧ hs = HardStateM.mk (W64 0) (W64 0) (W64 0)⌝ ∨ hsRO p hs)

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode

/-! ### Entry slices -/

instance entsRO_persistent (s : GoSlice) (es : List EntryM) :
    Persistent (entsRO (GF := GF) s es) := by
  unfold entsRO entsPts; infer_instance

theorem entsBig_length (ls : List Loc) (es : List EntryM) :
    ([∗list] l;e ∈ ls;es, entRO (GF := GF) l e) ⊢ ⌜ls.length = es.length⌝ :=
  BigSepL2.bigSepL2_length

/-- The length of an entry slice. -/
theorem entsPts_len (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPts (GF := GF) s dq es ⊢ ⌜es.length = sint.nat s.len ∧ 0 ≤ sint.Z s.len⌝ := by
  iintro H
  iunfold entsPts at H
  icases H with ⟨%ls, Hs, Hb⟩
  ihave %H1 := ownSlice_len $$ Hs
  ihave %H2 := entsBig_length $$ Hb
  ipureintro; omega

theorem entsPts_nil (dq : DFrac) : ⊢ entsPts (GF := GF) slice.nil dq [] := by
  iunfold entsPts
  iexists []
  isplitr
  · iapply ownSlice_nil
  · iapply BigSepL2.bigSepL2_nil.2; iempintro

theorem entsBig_nil : ⊢ ([∗list] l;e ∈ ([] : List Loc);([] : List EntryM), entRO (GF := GF) l e) :=
  BigSepL2.bigSepL2_nil.2

/-- The big separating conjunction of a concatenation. -/
theorem entsBig_app (ls1 ls2 : List Loc) (es1 es2 : List EntryM) :
    ([∗list] l;e ∈ ls1;es1, entRO (GF := GF) l e) ∗ ([∗list] l;e ∈ ls2;es2, entRO l e) ⊢
      [∗list] l;e ∈ ls1 ++ ls2;es1 ++ es2, entRO l e := by
  iintro ⟨#H1, #H2⟩
  ihave %Hl := entsBig_length $$ H1
  iapply (BigSepL2.bigSepL2_app_same_length (.inl Hl)).2
  iframe H1 H2

theorem entsBig_take (n : Nat) (ls : List Loc) (es : List EntryM) :
    ([∗list] l;e ∈ ls;es, entRO (GF := GF) l e) ⊢ [∗list] l;e ∈ ls.take n;es.take n, entRO l e := by
  iintro #H
  ihave %Hl := entsBig_length $$ H
  have Ht : (ls.take n).length = (es.take n).length := by simp [Hl]
  have Hd := (BigSepL2.bigSepL2_app_same_length (PROP := IProp GF)
    (Φ := fun _ l e => entRO (GF := GF) l e) (l1a := ls.take n) (l1b := ls.drop n)
    (l2a := es.take n) (l2b := es.drop n) (.inl Ht)).1
  rw [List.take_append_drop, List.take_append_drop] at Hd
  ihave H' := Hd $$ H
  icases H' with ⟨H1, -⟩
  iexact H1

theorem entsBig_drop (n : Nat) (ls : List Loc) (es : List EntryM) :
    ([∗list] l;e ∈ ls;es, entRO (GF := GF) l e) ⊢ [∗list] l;e ∈ ls.drop n;es.drop n, entRO l e := by
  iintro #H
  ihave %Hl := entsBig_length $$ H
  have Ht : (ls.take n).length = (es.take n).length := by simp [Hl]
  have Hd := (BigSepL2.bigSepL2_app_same_length (PROP := IProp GF)
    (Φ := fun _ l e => entRO (GF := GF) l e) (l1a := ls.take n) (l1b := ls.drop n)
    (l2a := es.take n) (l2b := es.drop n) (.inl Ht)).1
  rw [List.take_append_drop, List.take_append_drop] at Hd
  ihave H' := Hd $$ H
  icases H' with ⟨-, H2⟩
  iexact H2

theorem entsBig_subslice (lo hi : Nat) (ls : List Loc) (es : List EntryM) :
    ([∗list] l;e ∈ ls;es, entRO (GF := GF) l e) ⊢
      [∗list] l;e ∈ subslice lo hi ls;subslice lo hi es, entRO l e := by
  iintro #H
  simp only [subslice]
  iapply entsBig_drop
  iapply entsBig_take
  iexact H

/-- The entry at a position of the slice (the pointer loaded from it is a log entry). -/
theorem entsBig_lookup (ls : List Loc) (es : List EntryM) (i : Nat) (e : EntryM)
    (He : es[i]? = some e) :
    ([∗list] l;e ∈ ls;es, entRO (GF := GF) l e) ⊢ ∃ l, ⌜ls[i]? = some l⌝ ∗ entRO l e := by
  iintro #H
  ihave %Hl := entsBig_length $$ H
  have Hi : i < ls.length := by have := (List.getElem?_eq_some_iff.1 He).1; omega
  obtain ⟨l, Hl'⟩ : ∃ l, ls[i]? = some l := ⟨_, List.getElem?_eq_getElem Hi⟩
  iexists l
  isplitr
  · ipureintro; exact Hl'
  iapply (BigSepL2.bigSepL2_lookup Hl' He) $$ H

/-- Two lists of log entries at the same pointers are the same (D2: a log entry is one value
for good). -/
theorem entsBig_agree (ls : List Loc) (es1 es2 : List EntryM) :
    ([∗list] l;e ∈ ls;es1, entRO (GF := GF) l e) ∗ ([∗list] l;e ∈ ls;es2, entRO l e) ⊢
      ⌜es1 = es2⌝ := by
  induction ls generalizing es1 es2 with
  | nil =>
    iintro ⟨H1, H2⟩
    ihave %h1 := entsBig_length $$ H1
    ihave %h2 := entsBig_length $$ H2
    ipureintro
    cases es1 <;> cases es2 <;> simp_all
  | cons l ls ih =>
    cases es1 with
    | nil =>
      iintro ⟨H1, -⟩
      ihave %h1 := entsBig_length $$ H1
      simp at h1
    | cons e1 es1 =>
      cases es2 with
      | nil =>
        iintro ⟨-, H2⟩
        ihave %h2 := entsBig_length $$ H2
        simp at h2
      | cons e2 es2 =>
        iintro ⟨H1, H2⟩
        icases (BigSepL2.bigSepL2_cons).1 $$ H1 with ⟨#E1, #R1⟩
        icases (BigSepL2.bigSepL2_cons).1 $$ H2 with ⟨#E2, #R2⟩
        ihave %He := entPts_agree l DFrac.discard DFrac.discard e1 e2 $$ [E1 E2]
        · iframe E1 E2
        ihave %Hr := ih es1 es2 $$ [R1 R2]
        · iframe R1 R2
        ipureintro; rw [He, Hr]

/-- An entry slice, frozen read-only. -/
theorem entsPts_persist (s : GoSlice) (dq : DFrac) (es : List EntryM) :
    entsPts (GF := GF) s dq es ⊢ |==> entsRO s es := by
  iintro H
  iunfold entsPts at H
  icases H with ⟨%ls, Hs, #Hb⟩
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hs with #Hs
  imodintro
  unfold entsRO entsPts
  iexists ls
  iframe Hs Hb

/-! ### Hard states -/

instance hsOpt_persistent (p : Loc) (hs : HardStateM) : Persistent (hsOpt (GF := GF) p hs) := by
  unfold hsOpt; infer_instance

theorem hsOpt_null : ⊢ hsOpt (GF := GF) null (HardStateM.mk (W64 0) (W64 0) (W64 0)) := by
  iunfold hsOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩

/-! ### Read-only snapshots -/

instance csOpt_persistent (p : Loc) (c : ConfStateM) :
    Persistent (csOpt (GF := GF) p DFrac.discard c) := by
  unfold csOpt ownCSM; infer_instance

instance csOptA_persistent (p : Loc) (c : ConfStateM) :
    Persistent (csOptA (GF := GF) p DFrac.discard c) := by
  unfold csOptA; infer_instance

set_option synthInstance.maxSize 1024 in
instance smPts_persistent (p : Loc) (md : SnapshotMetadataM) :
    Persistent (smPts (GF := GF) p DFrac.discard md) := by
  unfold smPts; infer_instance

instance smOpt_persistent (p : Loc) (md : SnapshotMetadataM) :
    Persistent (smOpt (GF := GF) p DFrac.discard md) := by
  unfold smOpt; infer_instance

set_option synthInstance.maxSize 1024 in
instance ownSnapM_persistent (p : Loc) (s : SnapshotM) :
    Persistent (ownSnapM (GF := GF) p DFrac.discard s) := by
  unfold ownSnapM; infer_instance

theorem ownSnapE_weaken (p : Loc) (dq : DFrac) (s : SnapshotM) :
    ownSnapE (GF := GF) p dq s ⊢ ownSnapM p dq s := by
  iintro H
  iNamed H
  iunfold ownSnapM
  iexists ds, pm, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HD Hd HM Hpb
  iunfold smOpt
  iright; iexact Hm

/-- A freshly allocated `*pb.Snapshot` (hidden fields zero) whose data and (set) metadata hold
`s`'s. -/
theorem ownSnapE_of_struct (p : Loc) (v : raftpb.Snapshot) (s : SnapshotM) (E : CoPset)
    (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ v.Data' ↦* s.Data' ∗ smPts v.Metadata' (DFrac.own 1) s.Metadata' : IProp GF) ⊢
      |={E}=> ownSnapE p (DFrac.own 1) s := by
  iintro ⟨Hp, Hd, Hm⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Data, Metadata, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.Snapshot p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imodintro
  iunfold ownSnapE
  iexists v.Data', v.Metadata', []
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe Hpb

theorem csPts_persist (p : Loc) (dq : DFrac) (c : ConfStateM) (al : Bool) :
    csPts (GF := GF) p dq c al ⊢ |==> csPts p DFrac.discard c al := by
  iintro H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HV with #HV
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hv with #Hv
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HL with #HL
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hl with #Hl
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HO with #HO
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Ho with #Ho
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HN with #HN
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hn with #Hn
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HA with #HA
  imodintro
  iunfold csPts
  iexists sv, sl, so, sn, pa
  isplitr
  · ipureintro; exact Hnn
  iframe HV Hv HL Hl HO Ho HN Hn HA cA Hpb
  ipureintro; exact Hal

theorem csOpt_persist (p : Loc) (dq : DFrac) (c : ConfStateM) :
    csOpt (GF := GF) p dq c ⊢ |==> csOpt p DFrac.discard c := by
  iunfold csOpt
  iintro (%H | H)
  · imodintro; ileft; ipureintro; exact H
  · imod csPts_persist _ _ _ _ $$ H with #H
    imodintro; iright; iexact H

theorem csOptA_persist (p : Loc) (dq : DFrac) (c : ConfStateM) :
    csOptA (GF := GF) p dq c ⊢ |==> csOptA p DFrac.discard c := by
  iunfold csOptA
  iintro (%H | H | #H)
  · imodintro; ileft; ipureintro; exact H
  · imod csPts_persist _ _ _ _ $$ H with #H
    imodintro; iright; ileft; iexact H
  · imodintro; iright; iright; iexact H

theorem smPts_persist (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    smPts (GF := GF) p dq md ⊢ |==> smPts p DFrac.discard md := by
  iintro H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HC with #HC
  imod csOptA_persist _ _ _ $$ Hc with #Hc
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HI with #HI
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HT with #HT
  imodintro
  iunfold smPts
  iexists pc, pi, pt, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HC Hc HI cI HT cT Hpb

theorem smOpt_persist (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) :
    smOpt (GF := GF) p dq md ⊢ |==> smOpt p DFrac.discard md := by
  iunfold smOpt
  iintro (%H | H)
  · imodintro; ileft; ipureintro; exact H
  · imod smPts_persist _ _ _ $$ H with #H
    imodintro; iright; iexact H

/-- A snapshot frozen read-only (the log's pending snapshot: a fresh clone nothing writes after,
`log_unstable.go:196`). -/
theorem ownSnapM_persist (p : Loc) (dq : DFrac) (s : SnapshotM) :
    ownSnapM (GF := GF) p dq s ⊢ |==> ownSnapM p DFrac.discard s := by
  iintro H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HD with #HD
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hd with #Hd
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HM with #HM
  imod smOpt_persist _ _ _ $$ Hm with #Hm
  imodintro
  iunfold ownSnapM
  iexists ds, pm, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HD Hd HM Hm Hpb

end lemmas

end EtcdGrove
end Perennial
