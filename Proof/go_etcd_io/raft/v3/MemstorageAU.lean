/-
The logically atomic `MemoryStorage.{ApplySnapshot,CreateSnapshot,Compact}.spec` (D22 J3,
2026-10-26) and their corollaries: the triples of the token in hand
(`MemoryStorage.<M>.spec_tok`, the specs from D19i part 1 to D22 J3, word for word), which a caller
holding the whole token (`memSnapTok`) uses -- `examples/kv`'s `KV.run`, which runs the storage's
application and raft's loop in one goroutine. The AU is fired at once from the token in hand.

And the check that the AU forms serve a shared token (`memTokShared`, a small instance of D22 J4's
`srvStorTokInv`): `Compact` and `CreateSnapshot` against the token in an invariant, their premises
from the invariant's facts (`prev ≤ ss`, and a lower bound of `ss` kept by the caller), the
invariant kept (`MemoryStorage.Compact.wp_shared`, `MemoryStorage.CreateSnapshot.wp_shared`).
-/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__CreateSnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ms.ApplySnapshot(snap)` with the token in hand: `MemoryStorage.ApplySnapshot.spec` from D22
S-d4 to D22 J3 (see there). -/
abbrev MemoryStorage.ApplySnapshot.spec_tok : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σ σt : StorState) (sp : Loc) (sv : SnapshotM) (dq : DFrac)
    (eood : GoInterface),
  σ.pend = [] →
  uint.Z sv.Metadata'.Index' < 2^61 →
  -- (D19i part 1) the snapshot covers the floor
  uint.Z σ.fl ≤ uint.Z sv.Metadata'.Index' →
  -- (2026-10-19, D21 M3) and is within the storage's cap, the new boundary
  uint.Z sv.Metadata'.Index' ≤ γs.cap →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hms" ∷ ownMemoryStorage ms γs σ ∗
      "Htok" ∷ memSnapTok ms γs σt ∗
      "Hsnap" ∷ snapArg sp dq sv ∗
      -- (D22 S-b′2, 2026-10-20) the new snapshot certified in the storage's registry
      "#Hcert" ∷ memStorCert γs (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
      "#Herr" ∷ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"ApplySnapshot"))
      (Val #sp))
  {{ (err : GoInterface), RET #err;
      ownSnapM sp dq sv ∗
      ((⌜σt.ss.index' ≠ W64 0 ∧ uint.Z sv.Metadata'.Index' ≤ uint.Z σt.ss.index' ∧
          err = eood⌝ ∗
        ownMemoryStorage ms γs σ ∗ memSnapTok ms γs σt) ∨
      (⌜¬ (σt.ss.index' ≠ W64 0 ∧ uint.Z sv.Metadata'.Index' ≤ uint.Z σt.ss.index') ∧
          err = interface.nil⌝ ∗
        ownMemoryStorage ms γs { memStorApplied sv with fl := σ.fl } ∗
        memSnapTok ms γs (memStorApplied sv))) }}

/-- `ms.CreateSnapshot(i, cs, data)` with the token in hand: `MemoryStorage.CreateSnapshot.spec`
from D22 S-b′2 to D22 J3 (see there). -/
abbrev MemoryStorage.CreateSnapshot.spec_tok : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σt : StorState) (x i : w64) (cs : Loc) (dq : DFrac)
    (oc : Option ConfStateM) (data : GoSlice) (bs : List w8) (eood : GoInterface),
  (uint.Z σt.ss.index' < uint.Z i →
    uint.Z σt.prev.index' ≤ uint.Z i ∧ uint.Z i ≤ uint.Z x) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Htok" ∷ memSnapTok ms γs σt ∗
      "#Hfw" ∷ memFloorTok ms γs x ∗
      "Hcs" ∷ (match oc with
               | none => iprop(⌜cs = null⌝)
               | some c => ownCSM cs dq c) ∗
      "Hdata" ∷ data ↦* bs ∗
      -- (D22 S-b′2, 2026-10-20) the new snapshot certified in the storage's registry, at whatever
      -- term the storage has at `i` (the call reads it)
      "#Hcert" ∷ □ (∀ t : w64, memStorCert γs
        (snapTrip (memSnapCreated σt i t oc bs) (memSnapCreated σt i t oc bs).Metadata'.ConfState'.lists)) ∗
      "#Herr" ∷ globalAddr ErrSnapOutOfDate ↦□ eood }}
    (App (App (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"CreateSnapshot"))
      (Val #i)) (Val #cs)) (Val #data))
  {{ (snap' : Loc) (err : GoInterface), RET (PairV #snap' #err);
      (match oc with
       | none => iprop(⌜cs = null⌝)
       | some c => ownCSM cs dq c) ∗
      ((⌜uint.Z i ≤ uint.Z σt.ss.index' ∧ snap' = null ∧ err = eood⌝ ∗
        memSnapTok ms γs σt ∗ data ↦* bs) ∨
      (∃ (t : w64), ⌜uint.Z σt.ss.index' < uint.Z i ∧ err = interface.nil⌝ ∗
        ownSnapM snap' (DFrac.own 1) (memSnapCreated σt i t oc bs) ∗
        memSnapTok ms γs { σt with ss := entryID.mk t i,
                                   scs := (memSnapCreated σt i t oc bs).Metadata'.ConfState'.lists,
                                   sal := (memSnapCreated σt i t oc bs).Metadata'.ConfState'.AutoLeave',
                                   sdat := bs })) }}

omit [StorageModel GF] in
/-- `ms.Compact(ci)` with the token in hand: `MemoryStorage.Compact.spec` from D21 M3 to D22 J3
(see there). -/
abbrev MemoryStorage.Compact.spec_tok : Prop :=
  ∀ (ms : Loc) (γs : MemStorNames) (σt : StorState) (x ci : w64) (ecomp : GoInterface),
  (uint.Z σt.prev.index' < uint.Z ci →
    uint.Z ci ≤ uint.Z x ∧ uint.Z ci ≤ uint.Z σt.ss.index' ∧
    -- (2026-10-19, D21 M3) and within the storage's cap
    uint.Z ci ≤ γs.cap) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Htok" ∷ memSnapTok ms γs σt ∗
      "#Hfw" ∷ memFloorTok ms γs x ∗
      "#Herr" ∷ globalAddr ErrCompacted ↦□ ecomp }}
    (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Compact")) (Val #ci))
  {{ (err : GoInterface), RET #err;
      (⌜uint.Z ci ≤ uint.Z σt.prev.index' ∧ err = ecomp⌝ ∗ memSnapTok ms γs σt) ∨
      (∃ (t : w64), ⌜uint.Z σt.prev.index' < uint.Z ci ∧ err = interface.nil⌝ ∗
        memSnapTok ms γs { σt with prev := entryID.mk t ci }) }}

/-- (D22 J3) The check's shared token: the ghost part in an invariant, with the storage's snapshot
index counted (`γss`, the authority here, the caller's lower bounds outside) and the boundary at
or below the snapshot. A small instance of D22 J4's `srvStorTokInv`. -/
def memTokShared (γs : MemStorNames) (γss : GName) : IProp GF :=
  iprop(∃ σt : StorState, memSnapTokG γs σt ∗ monoNatAuthOwn γss 1 (uint.nat σt.ss.index') ∗
    ⌜uint.Z σt.prev.index' ≤ uint.Z σt.ss.index'⌝)

instance memTokShared_timeless (γs : MemStorNames) (γss : GName) :
    Timeless (memTokShared (GF := GF) γs γss) := by
  unfold memTokShared; infer_instance

end spec

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit [StorageModel GF] in
private theorem mask_empty_sub : (∅ : CoPset) ⊆ ⊤ \ ↑memSnapN := Std.LawfulSet.empty_subset

omit [StorageModel GF] in
/-- A Texan triple's later continuation (`▷ R`) used across the call's step: the call's own
postcondition needs `R`. What turns a logically atomic spec (no later) into a triple. -/
private theorem wp_later_frame {e : Expr} {Φ : val → IProp GF} {R : IProp GF}
    (h : toVal e = none) :
    ⊢ ▷ R -∗ WP e {{ v, R -∗ Φ v }} -∗ WP e {{ Φ }} := by
  iintro HR Hwp
  iapply (wp_wand (Φ := fun v => iprop(R ∗ (R -∗ Φ v)))) $$ [HR Hwp]
  · iapply (wp_frame_step_l' h (fun _ hp => hp))
    iframe
  · iintro %v ⟨HR, H⟩
    iapply H $$ HR

theorem MemoryStorage.ApplySnapshot.spec_tok_of
    (wp_ApplySnapshot : MemoryStorage.ApplySnapshot.spec (GF := GF) (hG := hG)) :
    MemoryStorage.ApplySnapshot.spec_tok (GF := GF) (hG := hG) := by
  intro ms γs σ σt sp sv dq eood Hidle Hbnd Hfl Hcap
  wp_start_folded as ⟨Hms, Htok, Hsnap, #Hcert, #Herr⟩
  icases (memSnapTok_split ms γs σt).1 $$ Htok with ⟨#Hro, Hak, Htg⟩
  iapply (wp_later_frame rfl) $$ HΦ
  iapply wp_ApplySnapshot ms γs σ sp sv dq eood Hidle Hbnd Hfl Hcap $$ [Hms Hsnap] [Hak Htg]
  · iframe Hpkg Hms Hsnap Hcert Herr
  iapply fupd_mask_intro mask_empty_sub
  iintro Hclose
  iexists σt
  iframe Htg
  isplit
  · iintro %Hood Htg
    imod Hclose with -
    imodintro
    iintro Hsnap Hms
    iintro HΦ
    iapply HΦ
    iframe Hsnap
    ileft
    isplitr
    · ipureintro; exact ⟨Hood.1, Hood.2, rfl⟩
    iframe Hms
    iapply (memSnapTok_split ms γs σt).2
    iframe Hro Hak Htg
  · iintro %Hnot Htg
    imod Hclose with -
    imodintro
    iintro Hsnap Hms
    iintro HΦ
    iapply HΦ
    iframe Hsnap
    iright
    isplitr
    · ipureintro; exact ⟨Hnot, rfl⟩
    iframe Hms
    iapply (memSnapTok_split ms γs _).2
    iframe Hro Hak Htg

theorem MemoryStorage.CreateSnapshot.spec_tok_of
    (wp_CreateSnapshot : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG)) :
    MemoryStorage.CreateSnapshot.spec_tok (GF := GF) (hG := hG) := by
  intro ms γs σt x i cs dq oc data bs eood Hpre
  wp_start_folded as ⟨Htok, #Hfw, Hcs, Hdata, #Hcert, #Herr⟩
  icases (memSnapTok_split ms γs σt).1 $$ Htok with ⟨#Hro, Hak, Htg⟩
  ihave Hcs : memCsArg cs dq oc $$ [Hcs]
  · cases oc <;> simp only [memCsArg] <;> iexact Hcs
  iapply (wp_later_frame rfl) $$ HΦ
  iapply wp_CreateSnapshot ms γs x i cs dq oc data bs eood $$ [Hak Hcs Hdata] [Htg]
  · iframe Hpkg Hro Hak Hfw Hcs Hdata Herr
  iapply fupd_mask_intro mask_empty_sub
  iintro Hclose
  iexists σt
  iframe Htg Hcert
  isplitr
  · ipureintro; exact Hpre
  isplit
  · iintro %Hle Htg
    imod Hclose with -
    imodintro
    iintro Hak Hcs Hdata
    iintro HΦ
    iapply HΦ
    isplitl [Hcs]
    · cases oc <;> simp only [memCsArg] <;> iexact Hcs
    ileft
    isplitr
    · ipureintro; exact ⟨Hle, rfl, rfl⟩
    iframe Hdata
    iapply (memSnapTok_split ms γs σt).2
    iframe Hro Hak Htg
  · iintro %t %Hlt Htg
    imod Hclose with -
    imodintro
    iintro %snap' Hsnap Hak Hcs
    iintro HΦ
    iapply HΦ
    isplitl [Hcs]
    · cases oc <;> simp only [memCsArg] <;> iexact Hcs
    iright
    iexists t
    isplitr
    · ipureintro; exact ⟨Hlt, rfl⟩
    iframe Hsnap
    iapply (memSnapTok_split ms γs _).2
    unfold memStorCreated
    iframe Hro Hak Htg

omit [StorageModel GF] in
theorem MemoryStorage.Compact.spec_tok_of
    (wp_Compact : MemoryStorage.Compact.spec (GF := GF) (hG := hG)) :
    MemoryStorage.Compact.spec_tok (GF := GF) (hG := hG) := by
  intro ms γs σt x ci ecomp Hpre
  wp_start_folded as ⟨Htok, #Hfw, #Herr⟩
  icases (memSnapTok_split ms γs σt).1 $$ Htok with ⟨#Hro, Hak, Htg⟩
  iapply (wp_later_frame rfl) $$ HΦ
  iapply wp_Compact ms γs x ci ecomp $$ [] [Hak Htg]
  · iframe Hpkg Hro Hfw Herr
  iapply fupd_mask_intro mask_empty_sub
  iintro Hclose
  iexists σt
  iframe Htg
  isplitr
  · ipureintro; exact Hpre
  isplit
  · iintro %Hle Htg
    imod Hclose with -
    imodintro
    iintro HΦ
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact ⟨Hle, rfl⟩
    iapply (memSnapTok_split ms γs σt).2
    iframe Hro Hak Htg
  · iintro %t %Hlt Htg
    imod Hclose with -
    imodintro
    iintro HΦ
    iapply HΦ
    iright
    iexists t
    isplitr
    · ipureintro; exact ⟨Hlt, rfl⟩
    iapply (memSnapTok_split ms γs _).2
    iframe Hro Hak Htg

/-! ### The check: the AU forms against a shared token (D22 J3)

The apply job's two calls in etcd's `snapshot`/`compactRaftLog`, with the token in an invariant
(`memTokShared`) that raft's goroutine shares (its `ApplySnapshot` keeps it: `prev = ss`): the
premises come from the invariant at the linearization point -- `Compact(ci)`'s `ci ≤ ss` from the
caller's lower bound of the snapshot counter, `CreateSnapshot(i)`'s `prev ≤ i` from `prev ≤ ss <
i` -- and each commit keeps the invariant (`Compact` raises `prev` to `ci ≤ ss`; `CreateSnapshot`
raises `ss` to `i`, which the counter follows, and hands the caller a lower bound at `i`). -/

omit [StorageModel GF] in
theorem MemoryStorage.Compact.wp_shared
    (wp_Compact : MemoryStorage.Compact.spec (GF := GF) (hG := hG))
    (N : Namespace) (HN : ↑N ## (↑memSnapN : CoPset))
    (ms : Loc) (γs : MemStorNames) (γss : GName) (x ci : w64) (sl : Nat) (ecomp : GoInterface)
    (Hx : uint.Z ci ≤ uint.Z x) (Hsl : uint.Z ci ≤ (sl : Int)) (Hcap : uint.Z ci ≤ γs.cap) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        memSnapRO ms γs ∗ memFloorTok ms γs x ∗ globalAddr ErrCompacted ↦□ ecomp ∗
        inv N (memTokShared γs γss) ∗ monoNatLbOwn γss sl }}
      (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Compact")) (Val #ci))
    {{ (err : GoInterface), RET #err; ⌜err = ecomp ∨ err = interface.nil⌝ }} := by
  wp_start_folded as ⟨#Hro, #Hfw, #Herr, #Hinv, #Hlb⟩
  iapply (wp_later_frame rfl) $$ HΦ
  iapply wp_Compact ms γs x ci ecomp $$ [] []
  · iframe Hpkg Hro Hfw Herr
  iinv Hinv with >Hi Hclose
  iunfold memTokShared at Hi
  icases Hi with ⟨%σt, Htg, Hss, %Hps⟩
  icases monoNatLbOwn_valid γss 1 _ sl $$ Hss Hlb with %Hv
  have Hsle := Hv.2
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists σt
  iframe Htg
  isplitr
  · ipureintro
    intro _
    refine ⟨Hx, ?_, Hcap⟩
    word
  isplit
  · iintro %Hle Htg
    imod Hclose2 with -
    imod Hclose $$ [Htg Hss] with -
    · inext
      iunfold memTokShared
      iexists σt
      iframe Htg Hss
      ipureintro; exact Hps
    imodintro
    iintro HΦ
    iapply HΦ
    ipureintro; left; rfl
  · iintro %t %Hlt Htg
    imod Hclose2 with -
    imod Hclose $$ [Htg Hss] with -
    · inext
      iunfold memTokShared
      iexists { σt with prev := entryID.mk t ci }
      iframe Htg Hss
      ipureintro
      show uint.Z ci ≤ uint.Z σt.ss.index'
      word
    imodintro
    iintro HΦ
    iapply HΦ
    ipureintro; right; rfl

omit [StorageModel GF] in
theorem MemoryStorage.CreateSnapshot.wp_shared
    (wp_CreateSnapshot : MemoryStorage.CreateSnapshot.spec (GF := GF) (hG := hG))
    (N : Namespace) (HN : ↑N ## (↑memSnapN : CoPset))
    (ms : Loc) (γs : MemStorNames) (γss : GName) (x i : w64) (cs : Loc) (dq : DFrac)
    (c : ConfStateM) (data : GoSlice) (bs : List w8) (eood : GoInterface)
    (Hx : uint.Z i ≤ uint.Z x) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        memSnapRO ms γs ∗ memKey γs.ak ∗ memFloorTok ms γs x ∗ ownCSM cs dq c ∗ data ↦* bs ∗
        globalAddr ErrSnapOutOfDate ↦□ eood ∗
        □ (∀ (σ : StorState) (t : w64), memStorCert γs (snapTrip (memSnapCreated σ i t (some c) bs)
          (memSnapCreated σ i t (some c) bs).Metadata'.ConfState'.lists)) ∗
        inv N (memTokShared γs γss) }}
      (App (App (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"CreateSnapshot"))
        (Val #i)) (Val #cs)) (Val #data))
    {{ (snap' : Loc) (err : GoInterface), RET (PairV #snap' #err);
        memKey γs.ak ∗ ownCSM cs dq c ∗ monoNatLbOwn γss (uint.nat i) ∗
        ((⌜err = eood⌝ ∗ data ↦* bs) ∨
         (⌜err = interface.nil⌝ ∗ ∃ σ t, ownSnapM snap' (DFrac.own 1) (memSnapCreated σ i t (some c) bs))) }} := by
  wp_start_folded as ⟨#Hro, Hak, #Hfw, Hcs, Hdata, #Herr, #Hcert, #Hinv⟩
  iapply (wp_later_frame rfl) $$ HΦ
  iapply wp_CreateSnapshot ms γs x i cs dq (some c) data bs eood $$ [Hak Hcs Hdata] []
  · iframe Hpkg Hro Hak Hfw Hdata Herr
    iunfold memCsArg
    iexact Hcs
  iinv Hinv with >Hi Hclose
  iunfold memTokShared at Hi
  icases Hi with ⟨%σt, Htg, Hss, %Hps⟩
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hclose2
  iexists σt
  iframe Htg
  isplitr
  · ipureintro
    intro Hlt
    exact ⟨by omega, Hx⟩
  isplitr
  · imodintro
    iintro %t
    iapply Hcert
  isplit
  · -- `ErrSnapOutOfDate`: the storage's snapshot is at or past `i`
    iintro %Hle Htg
    ihave #Hlbi : monoNatLbOwn γss (uint.nat i) $$ [Hss]
    · ihave #Hlb := monoNatLbOwn_get γss 1 _ $$ Hss
      iapply monoNatLbOwn_le (uint.nat i) (by word) $$ Hlb
    imod Hclose2 with -
    imod Hclose $$ [Htg Hss] with -
    · inext
      iunfold memTokShared
      iexists σt
      iframe Htg Hss
      ipureintro; exact Hps
    imodintro
    iintro Hak Hcs Hdata HΦ
    iapply HΦ
    iframe Hak Hlbi
    isplitl [Hcs]
    · iunfold memCsArg at Hcs; iexact Hcs
    ileft
    iframe Hdata
    ipureintro; rfl
  · -- the snapshot at `i`: the counter follows
    iintro %t %Hlt Htg
    imod mono_nat_own_update (uint.nat i) (by word) $$ Hss with ⟨Hss, #Hlbi⟩
    imod Hclose2 with -
    imod Hclose $$ [Htg Hss] with -
    · inext
      iunfold memTokShared
      iexists memStorCreated σt i t (some c) bs
      iframe Htg
      unfold memStorCreated
      iframe Hss
      ipureintro
      show uint.Z σt.prev.index' ≤ uint.Z i
      omega
    imodintro
    iintro %snap' Hsnap Hak Hcs HΦ
    iapply HΦ
    iframe Hak Hlbi
    isplitl [Hcs]
    · iunfold memCsArg at Hcs; iexact Hcs
    iright
    isplitr
    · ipureintro; rfl
    iexists σt, t
    iexact Hsnap

end proof

end EtcdGrove
end Perennial
