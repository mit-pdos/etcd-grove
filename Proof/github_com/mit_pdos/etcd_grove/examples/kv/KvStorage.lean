/-
Lean-first (no Rocq counterpart).

# The store's `Storage` and its `StorageModel` (2026-10-30, stage F of the client repair: copied
from kvreconf's `KvrStorage.lean`, kv's names)

`*kv.Storage` (`kv.go`) wraps a `MemoryStorage` (embedded, its methods promoted) and the cluster's
voters (`voters`, which its own `InitialState` answers as the configuration); its `Snapshot` says
`ErrSnapshotTemporarilyUnavailable` for a storage that never had one. raft's node API is stated
over a `StorageModel GF`; this file gives the store's, `kvStorageModel`, built as raft's
`memStorageModel` (`MemstorageInstance.lean`) is, over a **registry** keyed by the wrapper's
pointer: `kvStorRec s ms γs` (persistent) says the wrapper `s` holds the `MemoryStorage` `ms` with
the names `γs`. Then `storLog (kvStorIface s)`, `storEnd …`, `storCompacted …` are `ms`'s
`memLog γs`, `memEnd γs`, `memCompacted γs` (`kvStorLog_to/_of`, ...).

**Instance discipline.** Unlike kvreconf's, `kvStorageModel` is a global instance under
`[KVStor GF]` (as kv's was before the repair): kv's specs are stated over it. raft's own
`MemStorReg` is never in scope here, so `memStorJ`/`memStorInv` are not used: `kvJ γ id` is
`memStorJ`'s fields, and the storage's invariant is `memStorInvP ms γs (kvJ γ id)`.

**The registry's authority** is in an invariant (`kvStorInv`), with half of each registered
wrapper's `MemoryStorage` field: a wrapper whose field is still wholly owned (just allocated) is not
registered, so it can be (`kvStor_register`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Base
public import Proof.go_etcd_io.raft.v3.MemstorageInstance
public import Proof.go_etcd_io.raft.v3.InvNodeRule
public import Spec.google_golang_org.protobuf.proto.CloneConfState

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The store's `Storage` struct (not raft's `Storage` interface). -/
abbrev RStorage [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kv.Storage

abbrev rStorageTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kv.Storage.ty

/-- The registry's ghost name (a ghost map from a wrapper's pointer to its `MemoryStorage` and that
storage's names). -/
class KVStor (GF : BundledGFunctors) where
  kvStorName : GName

/-- A registered wrapper's record: its `MemoryStorage` and that storage's names. -/
abbrev KVStorRecT := Loc × MemStorNamesRec

def kvStorRecOf (ms : Loc) (γs : MemStorNames) : KVStorRecT := (ms, γs.tuple)

theorem kvStorRecOf_inj (ms1 ms2 : Loc) (γs1 γs2 : MemStorNames) :
    kvStorRecOf ms1 γs1 = kvStorRecOf ms2 γs2 → ms1 = ms2 ∧ γs1 = γs2 := by
  intro h
  simp only [kvStorRecOf, Prod.mk.injEq] at h
  exact ⟨h.1, MemStorNames.rec_inj _ _ h.2⟩

def kvStorN : Namespace := nroot.@"kv_storage"

section stor
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- The raft `Storage` interface value of the store's storage `s` (`Cluster.config`'s
`Storage: st`, `st : *Storage`). -/
def kvStorIface (s : Loc) : Storage :=
  interface.mkOk (go.GoType.PointerType rStorageTy) #s

include sem in
theorem kvStorIface_inj (s1 s2 : Loc) : kvStorIface s1 = kvStorIface s2 → s1 = s2 := by
  intro h
  simp only [kvStorIface, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    true_and] at h
  exact go.intoVal_inj h

/-- The wrapper `s` holds the `MemoryStorage` `ms`, whose names are `γs` (persistent). -/
def kvStorRec (s ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(s.[RStorage, go!"MemoryStorage"] ↦□ ms ∗
    s ↪[KVStor.kvStorName (GF := GF)]□ kvStorRecOf ms γs)

instance kvStorRec_persistent (s ms : Loc) (γs : MemStorNames) :
    Persistent (kvStorRec (GF := GF) s ms γs) := by
  unfold kvStorRec; infer_instance

theorem kvStorRec_agree (s ms1 ms2 : Loc) (γs1 γs2 : MemStorNames) :
    ⊢ kvStorRec (GF := GF) s ms1 γs1 -∗ kvStorRec s ms2 γs2 -∗ ⌜ms1 = ms2 ∧ γs1 = γs2⌝ := by
  unfold kvStorRec
  iintro ⟨-, #H1⟩ ⟨-, #H2⟩
  icases ghostMapElem_agree _ _ _ _ _ _ $$ H1 H2 with %H
  ipureintro; exact kvStorRecOf_inj _ _ _ _ H

/-- Two records of the same interface value agree. -/
theorem kvStorRec_same (st : Storage) (s1 s2 ms1 ms2 : Loc) (γs1 γs2 : MemStorNames)
    (h1 : st = kvStorIface s1) (h2 : st = kvStorIface s2) :
    ⊢ kvStorRec (GF := GF) s1 ms1 γs1 -∗ kvStorRec s2 ms2 γs2 -∗ ⌜ms1 = ms2 ∧ γs1 = γs2⌝ := by
  iintro #H1 #H2
  have := kvStorIface_inj (GF := GF) _ _ (h1.symm.trans h2)
  subst this
  iapply kvStorRec_agree s1 ms1 ms2 γs1 γs2 $$ H1 H2

/-- The registry: its authority, and half of each registered wrapper's `MemoryStorage` field (so a
wrapper is registered once). -/
def kvStorInvBody : IProp GF :=
  iprop(∃ M : GMap Loc KVStorRecT, ghostMapAuth (KVStor.kvStorName (GF := GF)) 1 M ∗
    [∗map] s ↦ x ∈ M,
      s.[RStorage, go!"MemoryStorage"]
        ↦{DFrac.own (1 : Qp).half} x.1)

def kvStorInv : IProp GF := inv kvStorN kvStorInvBody

instance kvStorInv_persistent : Persistent (kvStorInv (GF := GF)) := by
  unfold kvStorInv; infer_instance

instance kvStorInvBody_timeless : Timeless (kvStorInvBody (GF := GF)) := by
  unfold kvStorInvBody; infer_instance

/-- A pointer-valued location wholly owned has no other fraction. -/
theorem kvLoc_pointsto_excl (l : Loc) (v1 v2 : Loc) (q : Qp) :
    ⊢ (l ↦ v1 : IProp GF) -∗ l ↦{DFrac.own q} v2 -∗ False := by
  iintro H1 H2
  ihave H1 := typedPointsto_split _ _ _ $$ H1
  ihave H2 := typedPointsto_split _ _ _ $$ H2
  have h : ∀ (v : Loc) (dq : DFrac),
      typedPointstoDef (GF := GF) l v dq = heapPointsto l dq #v := fun _ _ => rfl
  rw [h, h]
  icombine H1 H2 gives %H
  exfalso
  have := DFrac.valid_own_op H.1
  have h1 : (1 : Qp).val = 1 := rfl
  have h2 : 0 < q.val := q.property
  grind

/-- **A new wrapper joins the registry**: its `MemoryStorage` field, still wholly owned (so the
wrapper is not registered yet), becomes the persistent record. -/
theorem kvStor_register (s ms : Loc) (γs : MemStorNames) (E : CoPset) (HE : ↑kvStorN ⊆ E) :
    ⊢ kvStorInv (GF := GF) -∗
      s.[RStorage, go!"MemoryStorage"] ↦ ms ={E}=∗
      kvStorRec s ms γs := by
  iintro #Hinv Hf
  unfold kvStorInv
  iinv Hinv with >Hi Hclose
  unfold kvStorInvBody
  icases Hi with ⟨%M, Ha, Hm⟩
  cases HM : M !! s with
  | some x =>
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun (s : Loc) (x : KVStorRecT) =>
      iprop(s.[RStorage, go!"MemoryStorage"]
        ↦{DFrac.own (1 : Qp).half} x.1)) HM).1 $$ Hm
      with ⟨Hx, -⟩
    iexfalso
    iapply kvLoc_pointsto_excl $$ Hf Hx
  | none =>
    imod ghost_map_insert_persist s (kvStorRecOf ms γs) HM $$ Ha with ⟨Ha, #Hfrag⟩
    icases (typedPointsto_dfractional (GF := GF)
      (s.[RStorage, go!"MemoryStorage"]) ms).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) |>.1 $$ [Hf] with ⟨Hf1, Hf2⟩
    · rw [DFrac.op_own, Qp.half_add_half]; iexact Hf
    imod (typedPointsto_dfractional (GF := GF) _ ms).dfractional_persist _ $$ Hf2 with #Hf2
    imod Hclose $$ [Ha Hm Hf1] with -
    · inext
      iexists M.insert s (kvStorRecOf ms γs)
      iframe Ha
      iapply (BigSepM.bigSepM_insert (Φ := fun (s : Loc) (x : KVStorRecT) =>
        iprop(s.[RStorage, go!"MemoryStorage"]
          ↦{DFrac.own (1 : Qp).half} x.1)) HM).2
      iframe Hm
      unfold kvStorRecOf
      iexact Hf1
    imodintro
    unfold kvStorRec
    iframe Hf2 Hfrag

/-! ### The vocabulary of a registered wrapper -/

/-- `storLog`: empty, or a registered wrapper's `MemoryStorage`'s range. -/
def kvStorLogI (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM) : IProp GF :=
  iprop(⌜es = []⌝ ∨ ∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kvStorIface s⌝ ∗
    kvStorRec s ms γs ∗ memLog γs k dq es)

/-- `storEnd`: a registered wrapper's `MemoryStorage`'s end. -/
def kvStorEndI (st : Storage) (e : Nat) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kvStorIface s⌝ ∗ kvStorRec s ms γs ∗
    memEnd γs e)

/-- `storCompacted`: `0`, or a registered wrapper's `MemoryStorage`'s compaction point. -/
def kvStorCompactedI (st : Storage) (c : Nat) : IProp GF :=
  iprop(⌜c = 0⌝ ∨ ∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kvStorIface s⌝ ∗
    kvStorRec s ms γs ∗ memCompacted γs c)

theorem kvStorLogI_app (st : Storage) (k : Nat) (dq : DFrac) (a b : List EntryM) :
    kvStorLogI (GF := GF) st k dq (a ++ b) ⊣⊢
      kvStorLogI st k dq a ∗ kvStorLogI st (k + a.length) dq b := by
  unfold kvStorLogI
  constructor
  · iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H⟩)
    · simp only [List.append_eq_nil_iff] at H
      isplitl [] <;> ileft <;> ipureintro
      · exact H.1
      · exact H.2
    icases (memLog_app γs k dq a b).1 $$ H with ⟨Ha, Hb⟩
    isplitl [Ha]
    · iright; iexists s, ms, γs; iframe Hreg Ha; ipureintro; exact Hst
    · iright; iexists s, ms, γs; iframe Hreg Hb; ipureintro; exact Hst
  · iintro ⟨Ha, Hb⟩
    icases Ha with (%Ha | ⟨%s, %ms, %γs, %Hst, #Hreg, Ha⟩)
    · subst Ha
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      iexact Hb
    icases Hb with (%Hb | ⟨%s', %ms', %γs', %Hst', #Hreg', Hb⟩)
    · subst Hb
      simp only [List.append_nil]
      iright; iexists s, ms, γs; iframe Hreg Ha; ipureintro; exact Hst
    icases kvStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
    obtain ⟨rfl, rfl⟩ := Hsame
    iright
    iexists s, ms, γs
    iframe Hreg
    isplitr
    · ipureintro; exact Hst
    iapply (memLog_app γs k dq a b).2
    iframe

theorem kvStorLogI_frac (st : Storage) (k : Nat) (dq1 dq2 : DFrac) (es : List EntryM) :
    kvStorLogI (GF := GF) st k (dq1 • dq2) es ⊣⊢
      kvStorLogI st k dq1 es ∗ kvStorLogI st k dq2 es := by
  unfold kvStorLogI
  constructor
  · iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H⟩)
    · isplitl [] <;> ileft <;> ipureintro <;> exact H
    icases (memLog_frac γs k dq1 dq2 es).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iright; iexists s, ms, γs; iframe Hreg H1; ipureintro; exact Hst
    · iright; iexists s, ms, γs; iframe Hreg H2; ipureintro; exact Hst
  · iintro ⟨H1, H2⟩
    icases H1 with (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H1⟩)
    · ileft; ipureintro; exact H
    icases H2 with (%H | ⟨%s', %ms', %γs', %Hst', #Hreg', H2⟩)
    · ileft; ipureintro; exact H
    icases kvStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
    obtain ⟨rfl, rfl⟩ := Hsame
    iright
    iexists s, ms, γs
    iframe Hreg
    isplitr
    · ipureintro; exact Hst
    iapply (memLog_frac γs k dq1 dq2 es).2
    iframe

theorem kvStorLogI_valid (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM)
    (hne : es ≠ []) : kvStorLogI (GF := GF) st k dq es ⊢ ⌜✓ dq⌝ := by
  unfold kvStorLogI memLog
  iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H, -⟩)
  · exact absurd H hne
  obtain ⟨e, es', rfl⟩ : ∃ e es', es = e :: es' := List.exists_cons_of_ne_nil hne
  simp only [memLogL]
  icases H with ⟨H1, -⟩
  iapply ghostMapElem_valid $$ H1

/-- Two ranges of one map agree where they overlap (raft's `memLogL_agree`, which is stated
under `[MemStorReg GF]`, not in scope here). -/
theorem kvLogL_agree (γ : GName) (k1 k2 : Nat) (dq1 dq2 : DFrac) (es1 es2 : List EntryM) :
    memLogL (GF := GF) γ k1 dq1 es1 ∗ memLogL γ k2 dq2 es2 ⊢ ⌜LogAgree k1 es1 k2 es2⌝ := by
  unfold LogAgree
  refine (forall_intro fun i => ?_).trans pure_forall.2
  refine (forall_intro fun e1 => ?_).trans pure_forall.2
  refine (forall_intro fun e2 => ?_).trans pure_forall.2
  by_cases h : k1 ≤ i ∧ k2 ≤ i ∧ es1[i - k1]? = some e1 ∧ es2[i - k2]? = some e2
  · obtain ⟨h1, h2, h3, h4⟩ := h
    have l1 := memLogL_lookup (GF := GF) γ k1 dq1 es1 (i - k1) e1 h3
    have l2 := memLogL_lookup (GF := GF) γ k2 dq2 es2 (i - k2) e2 h4
    rw [show k1 + (i - k1) = i by omega] at l1
    rw [show k2 + (i - k2) = i by omega] at l2
    refine (sep_mono l1 l2).trans ?_
    iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
    icases ghostMapElem_agree i γ dq1 dq2 e1 e2 $$ H1 H2 with %He
    ipureintro
    intro _ _ _ _; exact He
  · iintro -
    ipureintro
    intro a b c d; exact absurd ⟨a, b, c, d⟩ h

theorem kvStorLogI_agree (st : Storage) (k1 k2 : Nat) (dq1 dq2 : DFrac) (es1 es2 : List EntryM) :
    kvStorLogI (GF := GF) st k1 dq1 es1 ∗ kvStorLogI st k2 dq2 es2 ⊢ ⌜LogAgree k1 es1 k2 es2⌝ := by
  unfold kvStorLogI
  iintro ⟨H1, H2⟩
  icases H1 with (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H1⟩)
  · subst H; ipureintro; intro i e1 e2 _ _ h; simp at h
  icases H2 with (%H | ⟨%s', %ms', %γs', %Hst', #Hreg', H2⟩)
  · subst H; ipureintro; intro i e1 e2 _ _ _ h; simp at h
  icases kvStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  unfold memLog
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  iapply kvLogL_agree γs.log k1 k2 dq1 dq2 es1 es2
  iframe

theorem kvStorLogI_persist (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM) :
    kvStorLogI (GF := GF) st k dq es ⊢ |==> kvStorLogI st k DFrac.discard es := by
  unfold kvStorLogI
  iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H⟩)
  · imodintro; ileft; ipureintro; exact H
  imod memLog_persist γs k dq es $$ H with H
  imodintro
  iright; iexists s, ms, γs; iframe Hreg H; ipureintro; exact Hst

theorem kvStorEndI_excl (st : Storage) (e e' : Nat) :
    kvStorEndI (GF := GF) st e ∗ kvStorEndI st e' ⊢ False := by
  unfold kvStorEndI
  iintro ⟨⟨%s, %ms, %γs, %Hst, #Hreg, H1⟩, ⟨%s', %ms', %γs', %Hst', #Hreg', H2⟩⟩
  icases kvStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iapply memEnd_excl γs e e'
  iframe

theorem kvStorCompactedI_mono (st : Storage) (c c' : Nat) (h : c' ≤ c) :
    kvStorCompactedI (GF := GF) st c ⊢ kvStorCompactedI st c' := by
  unfold kvStorCompactedI
  iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, #H⟩)
  · ileft; ipureintro; omega
  iright; iexists s, ms, γs; iframe Hreg
  isplitr
  · ipureintro; exact Hst
  iapply memCompacted_mono γs c c' h $$ H

/-- **The store's storage model**: every `Storage` raft sees is a registered wrapper (a global
instance under `[KVStor GF]`). -/
instance kvStorageModel : StorageModel GF where
  storLog := kvStorLogI
  storEnd := kvStorEndI
  storCompacted := kvStorCompactedI
  storLog_app := kvStorLogI_app
  storLog_frac := kvStorLogI_frac
  storLog_valid := kvStorLogI_valid
  storLog_agree := kvStorLogI_agree
  storLog_persist := kvStorLogI_persist
  storLog_persistent := fun st k es => by unfold kvStorLogI; infer_instance
  storLog_nil := fun st k dq => by unfold kvStorLogI; iintro; ileft; ipureintro; rfl
  storEnd_excl := kvStorEndI_excl
  storCompacted_persistent := fun st c => by unfold kvStorCompactedI; infer_instance
  storCompacted_zero := fun st => by unfold kvStorCompactedI; iintro; ileft; ipureintro; rfl
  storCompacted_mono := kvStorCompactedI_mono

/-! ### The conversions, under the wrapper's record -/

section conv

theorem kvStorLog_to (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ storLog (kvStorIface s) k dq es -∗ memLog γs k dq es := by
  iintro #Hreg H
  ihave H : kvStorLogI (kvStorIface s) k dq es $$ [H]
  · iexact H
  unfold kvStorLogI
  icases H with (%H | ⟨%s', %ms', %γs', %Hst, #Hreg', H⟩)
  · subst H; iapply memLog_nil
  icases kvStorRec_same (kvStorIface s) s s' ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem kvStorLog_of (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ memLog γs k dq es -∗ storLog (kvStorIface s) k dq es := by
  iintro #Hreg H
  ihave H : kvStorLogI (GF := GF) (kvStorIface s) k dq es $$ [H]
  · unfold kvStorLogI; iright; iexists s, ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

theorem kvStorEnd_to (s ms : Loc) (γs : MemStorNames) (e : Nat) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ storEnd (kvStorIface s) e -∗ memEnd γs e := by
  iintro #Hreg H
  ihave H : kvStorEndI (kvStorIface s) e $$ [H]
  · iexact H
  unfold kvStorEndI
  icases H with ⟨%s', %ms', %γs', %Hst, #Hreg', H⟩
  icases kvStorRec_same (kvStorIface s) s s' ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem kvStorEnd_of (s ms : Loc) (γs : MemStorNames) (e : Nat) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ memEnd γs e -∗ storEnd (kvStorIface s) e := by
  iintro #Hreg H
  ihave H : kvStorEndI (GF := GF) (kvStorIface s) e $$ [H]
  · unfold kvStorEndI; iexists s, ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

theorem kvStorCompacted_to (s ms : Loc) (γs : MemStorNames) (c : Nat) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ storCompacted (kvStorIface s) c -∗ memCompacted γs c := by
  iintro #Hreg H
  ihave H : kvStorCompactedI (kvStorIface s) c $$ [H]
  · iexact H
  unfold kvStorCompactedI
  icases H with (%H | ⟨%s', %ms', %γs', %Hst, #Hreg', #H⟩)
  · subst H; iapply memCompacted_zero
  icases kvStorRec_same (kvStorIface s) s s' ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem kvStorCompacted_of (s ms : Loc) (γs : MemStorNames) (c : Nat) :
    ⊢ kvStorRec (GF := GF) s ms γs -∗ memCompacted γs c -∗ storCompacted (kvStorIface s) c := by
  iintro #Hreg #H
  ihave H : kvStorCompactedI (GF := GF) (kvStorIface s) c $$ []
  · unfold kvStorCompactedI; iright; iexists s, ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

end conv

end stor

/-! ### The API's justifications -/

section just
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- Node `id`'s justifications for its storage's `MemoryStorage` (raft's `memStorJ`, without its
registry): the stored snapshots valid, compaction within what node `id` applied or a snapshot it
handed out, a stored snapshot within what was delivered. -/
def kvJ (γ : Cluster) (id : w64) : MemJust GF where
  SV := snapshotValid γ
  B k := iprop(nodeAppliedLb γ id k ∨ snapGiven γ id k)
  DL := storDL γ id
  SV_pers := fun sv => by infer_instance
  B_pers := fun k => by infer_instance
  B_timeless := fun k => by infer_instance
  DL_pers := fun i => by unfold storDL; infer_instance

end just

end EtcdGrove
end Perennial
