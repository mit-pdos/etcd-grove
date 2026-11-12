/-
The mode-generic helpers of the four `MemoryStorage` methods that take a mode (`memStorAt`:
`Snapshot`, `ApplySnapshot`, `Compact`, `CreateSnapshot`; durability stage I, I-5, survey-storage
§5), so that each proof stays one proof over both modes. A method's mode splits
(`memStorAt_split`) into the lock, the justified points' part (`memJcAt`: attached, the invariant
and the call's bounds; detached, the authority of `jc`) and the snapshot's home as the call holds
it (`memHomeAt`: attached, nothing, the home is in the invariant; detached, the home). Under the
lock a proof takes the home out (`memSnap_take_at`), registers a justified point
(`memCompJust_register_at`, the detached bound moving to `max c k`) and puts a home back
(`memSnap_put_at`); `memStorFresh_of_at` gives the detached token back at the end. The home's
validity is `memValAt` out of `take` (attached, the stored snapshot's validity; detached, that it is
the token's snapshot) and `memValNew` into `put` (attached, the validity; detached, nothing).
-/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The justified points' part of a mode: attached, the storage's invariant and the call's bounds
`P`; detached at `c`, the authority of `jc` (`0` in it, every point at most `c`). -/
def memJcAt (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM))
    (P : IProp GF) : IProp GF :=
  match o with
  | some (c, _) => iprop(∃ (L : List Nat), monoListAuthOwn γs.jc 1 L ∗ ⌜0 ∈ L ∧ ∀ k ∈ L, k ≤ c⌝)
  | none => iprop(memStorInvP ms γs J ∗ P)

/-- The snapshot's home as a call holds it: attached, nothing (it is in the invariant); detached
at `sv`, the home. -/
def memHomeAt (ms : Loc) (γs : MemStorNames) (o : Option (Nat × SnapshotM)) : IProp GF :=
  match o with
  | some (_, sv) => iprop(memKey γs.hk ∗ ∃ (sp : Loc),
      ms.[MemoryStorage, go!"snapshot"] ↦ sp ∗ ownSnapM sp (DFrac.own 1) sv ∗
      ghostVar γs.sx (1 : Qp).half sv)
  | none => iprop(emp)

/-- The lock's key as a call holds it after `take`: attached, nothing (the invariant has it);
detached, the key (the lock's invariant needs it back at `Unlock`). -/
def memLkAt (γs : MemStorNames) (o : Option (Nat × SnapshotM)) : IProp GF :=
  match o with
  | some _ => memKey γs.lk
  | none => iprop(emp)

/-- The validity of the snapshot `take` finds at home: attached, the stored snapshot's validity;
detached, that it is the token's snapshot. -/
def memValAt (J : MemJust GF) (o : Option (Nat × SnapshotM)) (sv : SnapshotM) : IProp GF :=
  match o with
  | some (_, sv0) => iprop(⌜sv = sv0⌝)
  | none => iprop(⌜sv.Metadata'.Index' = W64 0⌝ ∨ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index'))

instance memValAt_persistent (J : MemJust GF) (o : Option (Nat × SnapshotM)) (sv : SnapshotM) :
    Persistent (memValAt J o sv) := by
  cases o with
  | none => unfold memValAt; infer_instance
  | some p => obtain ⟨_, _⟩ := p; unfold memValAt; infer_instance

/-- The validity `put` needs of the snapshot it puts home: attached, its validity; detached,
nothing. -/
def memValNew (J : MemJust GF) (o : Option (Nat × SnapshotM)) (sv : SnapshotM) : IProp GF :=
  match o with
  | some _ => iprop(True)
  | none => iprop(⌜sv.Metadata'.Index' = W64 0⌝ ∨ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index'))

/-- The snapshot out of its home, at a mode's validity (`memSnapHome` at `memValAt`). -/
def memSnapHomeAt (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM)) :
    IProp GF :=
  iprop(memKey γs.hk ∗ ∃ (sp : Loc) (sv : SnapshotM),
    ms.[MemoryStorage, go!"snapshot"] ↦ sp ∗ ownSnapM sp (DFrac.own 1) sv ∗
    ghostVar γs.sx (1 : Qp).half sv ∗ memValAt J o sv)

/-- The detached bound moved to `max c k` (registering `k`). -/
def memBumpAt (o : Option (Nat × SnapshotM)) (k : Nat) : Option (Nat × SnapshotM) :=
  o.map fun p => (max p.1 k, p.2)

/-- The detached snapshot replaced by `sv`. -/
def memSetAt (o : Option (Nat × SnapshotM)) (sv : SnapshotM) : Option (Nat × SnapshotM) :=
  o.map fun p => (p.1, sv)

/-- Registering does not change whether the call is detached. -/
theorem memLkAt_bump (γs : MemStorNames) (o : Option (Nat × SnapshotM)) (k : Nat) :
    memLkAt (GF := GF) γs (memBumpAt o k) = memLkAt γs o := by
  cases o <;> rfl

theorem memValNew_bump (J : MemJust GF) (o : Option (Nat × SnapshotM)) (k : Nat) (sv : SnapshotM) :
    memValNew J (memBumpAt o k) sv = memValNew J o sv := by
  cases o <;> rfl

/-- **A mode, split**: the lock, the justified points' part and the home as the call holds it. -/
theorem memStorAt_split (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM))
    (P : IProp GF) :
    memStorAt ms γs J o P ⊢ memStorLock ms γs ∗ memJcAt ms γs J o P ∗ memHomeAt ms γs o := by
  cases o with
  | none =>
    rw [memStorAt_none]
    simp only [memJcAt, memHomeAt]
    iintro ⟨#Hi, HP⟩
    ihave #Hi2 := Hi
    iunfold memStorInvP at Hi2
    icases Hi2 with ⟨#Hl, -, -⟩
    iframe Hl Hi HP
  | some p =>
    obtain ⟨c, sv⟩ := p
    rw [memStorAt_some]
    simp only [memJcAt, memHomeAt, memStorFresh]
    iintro ⟨#Hl, Hj, Hh⟩
    iframe Hl Hj Hh

/-- The mode's validity at `take` gives the one at `put` (the snapshot put back unchanged). -/
theorem memValAt_new (J : MemJust GF) (o : Option (Nat × SnapshotM)) (sv : SnapshotM) :
    memValAt J o sv ⊢ memValNew J o sv := by
  cases o with
  | none => unfold memValAt memValNew; iintro H; iexact H
  | some p => obtain ⟨_, _⟩ := p; unfold memValAt memValNew; iintro -; ipureintro; trivial

/-- A new snapshot's validity at `put`, from the call's bounds (attached; nothing detached). -/
theorem memValNew_of_bound (ms : Loc) (γs : MemStorNames) (J : MemJust GF)
    (o : Option (Nat × SnapshotM)) (P : IProp GF) [Persistent P] (sv : SnapshotM)
    (hV : P ⊢ iprop(⌜sv.Metadata'.Index' = W64 0⌝ ∨ J.SV sv ∗ J.DL (uint.nat sv.Metadata'.Index'))) :
    memJcAt ms γs J o P ⊢ memJcAt ms γs J o P ∗ memValNew J o sv := by
  cases o with
  | none =>
    simp only [memJcAt, memValNew]
    iintro ⟨#Hi, #HP⟩
    iframe Hi HP
    iapply hV $$ HP
  | some p =>
    obtain ⟨_, _⟩ := p
    simp only [memJcAt, memValNew]
    iintro H
    iframe H

/-- **Take the snapshot out of its home** (mode-generic): attached, `memSnap_take` (the lock's key
into the invariant); detached, the home the call holds (the key stays with the call). -/
theorem memSnap_take_at (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM))
    (P : IProp GF) (E : CoPset) (hE : ↑memStorN ⊆ E) :
    ⊢ memJcAt ms γs J o P -∗ memHomeAt ms γs o -∗ memKey γs.lk ={E}=∗
      memJcAt ms γs J o P ∗ memLkAt γs o ∗ ▷ memSnapHomeAt ms γs J o := by
  cases o with
  | none =>
    simp only [memJcAt, memHomeAt, memLkAt]
    iintro ⟨#Hi, HP⟩ - Hlk
    imod memSnap_take ms γs J E hE $$ Hi Hlk with Hh
    imodintro
    iframe Hi HP
    isplitr
    · iempintro
    inext
    iunfold memSnapHome at Hh
    iunfold memSnapHomeAt
    simp only [memValAt]
    iexact Hh
  | some p =>
    obtain ⟨c, sv⟩ := p
    simp only [memJcAt, memHomeAt, memLkAt]
    iintro Hj ⟨Hhk, %sp, Hs, Hsnap, Hsx⟩ Hlk
    imodintro
    iframe Hj Hlk
    inext
    iunfold memSnapHomeAt
    iframe Hhk
    iexists sp, sv
    iframe Hs Hsnap Hsx
    simp only [memValAt]
    ipureintro; trivial

/-- **Put a snapshot `sv` home** (mode-generic): attached, `memSnap_put` at its validity (the lock's
key back from the invariant); detached, the call's home now at `sv` (and its key). -/
theorem memSnap_put_at (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM))
    (P : IProp GF) (E : CoPset) (hE : ↑memStorN ⊆ E) (sv : SnapshotM) (sp : Loc) :
    ⊢ memJcAt ms γs J o P -∗ memLkAt γs o -∗ memKey γs.hk -∗
      ms.[MemoryStorage, go!"snapshot"] ↦ sp -∗ ownSnapM sp (DFrac.own 1) sv -∗
      ghostVar γs.sx (1 : Qp).half sv -∗ memValNew J o sv ={E}=∗
      memJcAt ms γs J o P ∗ memKey γs.lk ∗ memHomeAt ms γs (memSetAt o sv) := by
  cases o with
  | none =>
    simp only [memJcAt, memLkAt, memValNew]
    iintro ⟨#Hi, HP⟩ - Hhk Hs Hsnap Hsx Hv
    imod memSnap_put ms γs J E hE $$ Hi [Hhk Hs Hsnap Hsx Hv] with Hlk
    · iunfold memSnapHome
      iframe Hhk
      iexists sp, sv
      iframe
    imodintro
    iframe Hi HP Hlk
    simp only [memSetAt, Option.map_none]
    simp only [memHomeAt]
    iempintro
  | some p =>
    obtain ⟨c, sv0⟩ := p
    simp only [memJcAt, memLkAt]
    iintro Hj Hlk Hhk Hs Hsnap Hsx -
    imodintro
    iframe Hj Hlk
    simp only [memSetAt, Option.map_some]
    simp only [memHomeAt]
    iframe Hhk
    iexists sp
    iframe

/-- **Register a justified compaction point `k`** (mode-generic): attached, `memCompJust_register`
from the call's bounds; detached, `k` appended to `jc`, the bound moving to `max c k`. -/
theorem memCompJust_register_at (ms : Loc) (γs : MemStorNames) (J : MemJust GF)
    (o : Option (Nat × SnapshotM)) (P : IProp GF) [Persistent P] (k : Nat) (E : CoPset)
    (hE : ↑memStorN ⊆ E) (hB : P ⊢ J.B k) :
    ⊢ memJcAt ms γs J o P ={E}=∗ memCompJust γs k ∗ memJcAt ms γs J (memBumpAt o k) P := by
  cases o with
  | none =>
    simp only [memBumpAt, Option.map_none]
    simp only [memJcAt]
    iintro ⟨#Hi, #HP⟩
    ihave #HB := hB $$ HP
    imod memCompJust_register ms γs J k E hE $$ Hi HB with #Hc
    imodintro
    iframe Hc Hi HP
  | some p =>
    obtain ⟨c, sv⟩ := p
    simp only [memBumpAt, Option.map_some]
    simp only [memJcAt]
    iintro ⟨%L, Ha, %HL⟩
    imod monoListAuthOwn_update_app [k] $$ Ha with ⟨Ha, #Hlb⟩
    imodintro
    isplitr
    · iunfold memCompJust
      iexists L ++ [k]
      iframe Hlb
      ipureintro; simp
    iexists L ++ [k]
    iframe Ha
    ipureintro
    refine ⟨List.mem_append_left _ HL.1, fun k' hk' => ?_⟩
    rcases List.mem_append.1 hk' with h | h
    · have := HL.2 k' h; omega
    · simp at h; omega

/-- The detached bound weakened to `max c k` (nothing registered). -/
theorem memJcAt_bump (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (o : Option (Nat × SnapshotM))
    (P : IProp GF) (k : Nat) :
    memJcAt ms γs J o P ⊢ memJcAt ms γs J (memBumpAt o k) P := by
  cases o with
  | none => simp only [memBumpAt, Option.map_none]; iintro H; iexact H
  | some p =>
    obtain ⟨c, sv⟩ := p
    simp only [memBumpAt, Option.map_some, memJcAt]
    iintro ⟨%L, Ha, %HL⟩
    iexists L
    iframe Ha
    ipureintro
    exact ⟨HL.1, fun k' hk' => by have := HL.2 k' hk'; omega⟩

/-- **The detached token back** at the end of a call: the justified points' part at `c` and the
home at `sv`. -/
theorem memStorFresh_of_at (ms : Loc) (γs : MemStorNames) (J : MemJust GF) (P : IProp GF)
    (c : Nat) (sv1 : SnapshotM) (c2 : Nat) (sv : SnapshotM) :
    memJcAt ms γs J (some (c, sv1)) P ∗ memHomeAt ms γs (some (c2, sv)) ⊢ memStorFresh ms γs c sv := by
  simp only [memJcAt, memHomeAt, memStorFresh]
  iintro ⟨Hj, Hh⟩
  iframe Hj Hh

end proof

end EtcdGrove
end Perennial
