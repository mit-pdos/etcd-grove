/-
Lean-first (no Rocq counterpart).

# The store's `Storage` and its `StorageModel` (2026-10-29, kvreconf's adequacy, helper T1)

`*kvreconf.Storage` (`kv.go`) wraps a `MemoryStorage` (embedded, its methods promoted) and the
bootstrap `ConfState` (`boot`, which its own `InitialState` clones); its `Snapshot` may say
`ErrSnapshotTemporarilyUnavailable`. raft's node API is stated over a `StorageModel GF`; this file
gives the store's, `kvrStorageModel`, built as raft's `memStorageModel` (`MemstorageInstance.lean`)
is, over a **registry** keyed by the wrapper's pointer: `kvrStorRec s ms γs` (persistent) says the
wrapper `s` holds the `MemoryStorage` `ms` with the names `γs`. Then `storLog (kvrStorIface s)`,
`storEnd …`, `storCompacted …` are `ms`'s `memLog γs`, `memEnd γs`, `memCompacted γs`
(`kvrStorLog_to/_of`, ...).

**Instance discipline.** `kvrStorageModel` is a `def`, not a global instance: a file that needs it
says `attribute [local instance] kvrStorageModel`; the rest of kvreconf stays generic over
`[StorageModel GF]`. raft's own `MemStorReg` is never in scope here, so `memStorJ`/`memStorInv` are
not used: `kvrJ γ id` is `memStorJ`'s fields, and the storage's invariant is `memStorInvP ms γs
(kvrJ γ id)`.

**The registry's authority** is in an invariant (`kvrStorInv`), with half of each registered
wrapper's `MemoryStorage` field: a wrapper whose field is still wholly owned (just allocated) is not
registered, so it can be (`kvr_register`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base
public import Proof.go_etcd_io.raft.v3.MemstorageInstance
public import Proof.go_etcd_io.raft.v3.InvNodeRule
public import Spec.google_golang_org.protobuf.proto.CloneConfState

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The registry's ghost name (a ghost map from a wrapper's pointer to its `MemoryStorage` and that
storage's names). -/
class KvrStor (GF : BundledGFunctors) where
  kvrStorName : GName

/-- A registered wrapper's record: its `MemoryStorage` and that storage's names. -/
abbrev KvrStorRecT := Loc × MemStorNamesRec

def kvrStorRecOf (ms : Loc) (γs : MemStorNames) : KvrStorRecT := (ms, γs.tuple)

theorem kvrStorRecOf_inj (ms1 ms2 : Loc) (γs1 γs2 : MemStorNames) :
    kvrStorRecOf ms1 γs1 = kvrStorRecOf ms2 γs2 → ms1 = ms2 ∧ γs1 = γs2 := by
  intro h
  simp only [kvrStorRecOf, Prod.mk.injEq] at h
  exact ⟨h.1, MemStorNames.rec_inj _ _ h.2⟩

def kvrStorN : Namespace := nroot.@"kvreconf_storage"

section stor
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [KvrStor GF]

/-- The raft `Storage` interface value of the store's storage `s` (`Cluster.config`'s
`Storage: st`, `st : *Storage`). -/
def kvrStorIface (s : Loc) : Storage :=
  interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty) #s

include sem in
theorem kvrStorIface_inj (s1 s2 : Loc) : kvrStorIface s1 = kvrStorIface s2 → s1 = s2 := by
  intro h
  simp only [kvrStorIface, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    true_and] at h
  exact go.intoVal_inj h

/-- The wrapper `s` holds the `MemoryStorage` `ms`, whose names are `γs` (persistent). -/
def kvrStorRec (s ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(s.[github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage, go!"MemoryStorage"] ↦□ ms ∗
    s ↪[KvrStor.kvrStorName (GF := GF)]□ kvrStorRecOf ms γs)

instance kvrStorRec_persistent (s ms : Loc) (γs : MemStorNames) :
    Persistent (kvrStorRec (GF := GF) s ms γs) := by
  unfold kvrStorRec; infer_instance

theorem kvrStorRec_agree (s ms1 ms2 : Loc) (γs1 γs2 : MemStorNames) :
    ⊢ kvrStorRec (GF := GF) s ms1 γs1 -∗ kvrStorRec s ms2 γs2 -∗ ⌜ms1 = ms2 ∧ γs1 = γs2⌝ := by
  unfold kvrStorRec
  iintro ⟨-, #H1⟩ ⟨-, #H2⟩
  icases ghostMapElem_agree _ _ _ _ _ _ $$ H1 H2 with %H
  ipureintro; exact kvrStorRecOf_inj _ _ _ _ H

/-- Two records of the same interface value agree. -/
theorem kvrStorRec_same (st : Storage) (s1 s2 ms1 ms2 : Loc) (γs1 γs2 : MemStorNames)
    (h1 : st = kvrStorIface s1) (h2 : st = kvrStorIface s2) :
    ⊢ kvrStorRec (GF := GF) s1 ms1 γs1 -∗ kvrStorRec s2 ms2 γs2 -∗ ⌜ms1 = ms2 ∧ γs1 = γs2⌝ := by
  iintro #H1 #H2
  have := kvrStorIface_inj (GF := GF) _ _ (h1.symm.trans h2)
  subst this
  iapply kvrStorRec_agree s1 ms1 ms2 γs1 γs2 $$ H1 H2

/-- The wrapper's bootstrap conf state (persistent): its `boot` field, a read-only `ConfState`
holding `csm` (what `proto.CloneConfState.spec` reads). -/
def kvrStorBoot (s bp : Loc) (csm : ConfStateM) : IProp GF :=
  iprop(s.[github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage, go!"boot"] ↦□ bp ∗
    ownCSM bp DFrac.discard csm)

instance kvrStorBoot_persistent (s bp : Loc) (csm : ConfStateM) :
    Persistent (kvrStorBoot (GF := GF) s bp csm) := by
  unfold kvrStorBoot ownCSM; infer_instance

/-- The registry: its authority, and half of each registered wrapper's `MemoryStorage` field (so a
wrapper is registered once). -/
def kvrStorInvBody : IProp GF :=
  iprop(∃ M : GMap Loc KvrStorRecT, ghostMapAuth (KvrStor.kvrStorName (GF := GF)) 1 M ∗
    [∗map] s ↦ x ∈ M,
      s.[github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage, go!"MemoryStorage"]
        ↦{DFrac.own (1 : Qp).half} x.1)

def kvrStorInv : IProp GF := inv kvrStorN kvrStorInvBody

instance kvrStorInv_persistent : Persistent (kvrStorInv (GF := GF)) := by
  unfold kvrStorInv; infer_instance

instance kvrStorInvBody_timeless : Timeless (kvrStorInvBody (GF := GF)) := by
  unfold kvrStorInvBody; infer_instance

/-- A pointer-valued location wholly owned has no other fraction. -/
theorem kvrLoc_pointsto_excl (l : Loc) (v1 v2 : Loc) (q : Qp) :
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
theorem kvrStor_register (s ms : Loc) (γs : MemStorNames) (E : CoPset) (HE : ↑kvrStorN ⊆ E) :
    ⊢ kvrStorInv (GF := GF) -∗
      s.[github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage, go!"MemoryStorage"] ↦ ms ={E}=∗
      kvrStorRec s ms γs := by
  iintro #Hinv Hf
  unfold kvrStorInv
  iinv Hinv with >Hi Hclose
  unfold kvrStorInvBody
  icases Hi with ⟨%M, Ha, Hm⟩
  cases HM : M !! s with
  | some x =>
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun (s : Loc) (x : KvrStorRecT) =>
      iprop(s.[github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage, go!"MemoryStorage"]
        ↦{DFrac.own (1 : Qp).half} x.1)) HM).1 $$ Hm
      with ⟨Hx, -⟩
    iexfalso
    iapply kvrLoc_pointsto_excl $$ Hf Hx
  | none =>
    imod ghost_map_insert_persist s (kvrStorRecOf ms γs) HM $$ Ha with ⟨Ha, #Hfrag⟩
    icases (typedPointsto_dfractional (GF := GF)
      (s.[github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage, go!"MemoryStorage"]) ms).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) |>.1 $$ [Hf] with ⟨Hf1, Hf2⟩
    · rw [DFrac.op_own, Qp.half_add_half]; iexact Hf
    imod (typedPointsto_dfractional (GF := GF) _ ms).dfractional_persist _ $$ Hf2 with #Hf2
    imod Hclose $$ [Ha Hm Hf1] with -
    · inext
      iexists M.insert s (kvrStorRecOf ms γs)
      iframe Ha
      iapply (BigSepM.bigSepM_insert (Φ := fun (s : Loc) (x : KvrStorRecT) =>
        iprop(s.[github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage, go!"MemoryStorage"]
          ↦{DFrac.own (1 : Qp).half} x.1)) HM).2
      iframe Hm
      unfold kvrStorRecOf
      iexact Hf1
    imodintro
    unfold kvrStorRec
    iframe Hf2 Hfrag

/-! ### The vocabulary of a registered wrapper -/

/-- `storLog`: empty, or a registered wrapper's `MemoryStorage`'s range. -/
def kvrStorLogI (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM) : IProp GF :=
  iprop(⌜es = []⌝ ∨ ∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kvrStorIface s⌝ ∗
    kvrStorRec s ms γs ∗ memLog γs k dq es)

/-- `storEnd`: a registered wrapper's `MemoryStorage`'s end. -/
def kvrStorEndI (st : Storage) (e : Nat) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kvrStorIface s⌝ ∗ kvrStorRec s ms γs ∗
    memEnd γs e)

/-- `storCompacted`: `0`, or a registered wrapper's `MemoryStorage`'s compaction point. -/
def kvrStorCompactedI (st : Storage) (c : Nat) : IProp GF :=
  iprop(⌜c = 0⌝ ∨ ∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kvrStorIface s⌝ ∗
    kvrStorRec s ms γs ∗ memCompacted γs c)

theorem kvrStorLogI_app (st : Storage) (k : Nat) (dq : DFrac) (a b : List EntryM) :
    kvrStorLogI (GF := GF) st k dq (a ++ b) ⊣⊢
      kvrStorLogI st k dq a ∗ kvrStorLogI st (k + a.length) dq b := by
  unfold kvrStorLogI
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
    icases kvrStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
    obtain ⟨rfl, rfl⟩ := Hsame
    iright
    iexists s, ms, γs
    iframe Hreg
    isplitr
    · ipureintro; exact Hst
    iapply (memLog_app γs k dq a b).2
    iframe

theorem kvrStorLogI_frac (st : Storage) (k : Nat) (dq1 dq2 : DFrac) (es : List EntryM) :
    kvrStorLogI (GF := GF) st k (dq1 • dq2) es ⊣⊢
      kvrStorLogI st k dq1 es ∗ kvrStorLogI st k dq2 es := by
  unfold kvrStorLogI
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
    icases kvrStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
    obtain ⟨rfl, rfl⟩ := Hsame
    iright
    iexists s, ms, γs
    iframe Hreg
    isplitr
    · ipureintro; exact Hst
    iapply (memLog_frac γs k dq1 dq2 es).2
    iframe

theorem kvrStorLogI_valid (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM)
    (hne : es ≠ []) : kvrStorLogI (GF := GF) st k dq es ⊢ ⌜✓ dq⌝ := by
  unfold kvrStorLogI memLog
  iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H, -⟩)
  · exact absurd H hne
  obtain ⟨e, es', rfl⟩ : ∃ e es', es = e :: es' := List.exists_cons_of_ne_nil hne
  simp only [memLogL]
  icases H with ⟨H1, -⟩
  iapply ghostMapElem_valid $$ H1

/-- Two ranges of one map agree where they overlap (raft's `memLogL_agree`, which is stated
under `[MemStorReg GF]`, not in scope here). -/
theorem kvrLogL_agree (γ : GName) (k1 k2 : Nat) (dq1 dq2 : DFrac) (es1 es2 : List EntryM) :
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

theorem kvrStorLogI_agree (st : Storage) (k1 k2 : Nat) (dq1 dq2 : DFrac) (es1 es2 : List EntryM) :
    kvrStorLogI (GF := GF) st k1 dq1 es1 ∗ kvrStorLogI st k2 dq2 es2 ⊢ ⌜LogAgree k1 es1 k2 es2⌝ := by
  unfold kvrStorLogI
  iintro ⟨H1, H2⟩
  icases H1 with (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H1⟩)
  · subst H; ipureintro; intro i e1 e2 _ _ h; simp at h
  icases H2 with (%H | ⟨%s', %ms', %γs', %Hst', #Hreg', H2⟩)
  · subst H; ipureintro; intro i e1 e2 _ _ _ h; simp at h
  icases kvrStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  unfold memLog
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  iapply kvrLogL_agree γs.log k1 k2 dq1 dq2 es1 es2
  iframe

theorem kvrStorLogI_persist (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM) :
    kvrStorLogI (GF := GF) st k dq es ⊢ |==> kvrStorLogI st k DFrac.discard es := by
  unfold kvrStorLogI
  iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H⟩)
  · imodintro; ileft; ipureintro; exact H
  imod memLog_persist γs k dq es $$ H with H
  imodintro
  iright; iexists s, ms, γs; iframe Hreg H; ipureintro; exact Hst

theorem kvrStorEndI_excl (st : Storage) (e e' : Nat) :
    kvrStorEndI (GF := GF) st e ∗ kvrStorEndI st e' ⊢ False := by
  unfold kvrStorEndI
  iintro ⟨⟨%s, %ms, %γs, %Hst, #Hreg, H1⟩, ⟨%s', %ms', %γs', %Hst', #Hreg', H2⟩⟩
  icases kvrStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iapply memEnd_excl γs e e'
  iframe

theorem kvrStorCompactedI_mono (st : Storage) (c c' : Nat) (h : c' ≤ c) :
    kvrStorCompactedI (GF := GF) st c ⊢ kvrStorCompactedI st c' := by
  unfold kvrStorCompactedI
  iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, #H⟩)
  · ileft; ipureintro; omega
  iright; iexists s, ms, γs; iframe Hreg
  isplitr
  · ipureintro; exact Hst
  iapply memCompacted_mono γs c c' h $$ H

/-- **The store's storage model**: every `Storage` raft sees is a registered wrapper. A `def`, made
an instance locally by the files that need it (`attribute [local instance] kvrStorageModel`). -/
@[instance_reducible]
def kvrStorageModel : StorageModel GF where
  storLog := kvrStorLogI
  storEnd := kvrStorEndI
  storCompacted := kvrStorCompactedI
  storLog_app := kvrStorLogI_app
  storLog_frac := kvrStorLogI_frac
  storLog_valid := kvrStorLogI_valid
  storLog_agree := kvrStorLogI_agree
  storLog_persist := kvrStorLogI_persist
  storLog_persistent := fun st k es => by unfold kvrStorLogI; infer_instance
  storLog_nil := fun st k dq => by unfold kvrStorLogI; iintro; ileft; ipureintro; rfl
  storEnd_excl := kvrStorEndI_excl
  storCompacted_persistent := fun st c => by unfold kvrStorCompactedI; infer_instance
  storCompacted_zero := fun st => by unfold kvrStorCompactedI; iintro; ileft; ipureintro; rfl
  storCompacted_mono := kvrStorCompactedI_mono

/-! ### The conversions, under the wrapper's record -/

section conv
attribute [local instance] kvrStorageModel

theorem kvrStorLog_to (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ kvrStorRec (GF := GF) s ms γs -∗ storLog (kvrStorIface s) k dq es -∗ memLog γs k dq es := by
  iintro #Hreg H
  ihave H : kvrStorLogI (kvrStorIface s) k dq es $$ [H]
  · iexact H
  unfold kvrStorLogI
  icases H with (%H | ⟨%s', %ms', %γs', %Hst, #Hreg', H⟩)
  · subst H; iapply memLog_nil
  icases kvrStorRec_same (kvrStorIface s) s s' ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem kvrStorLog_of (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ kvrStorRec (GF := GF) s ms γs -∗ memLog γs k dq es -∗ storLog (kvrStorIface s) k dq es := by
  iintro #Hreg H
  ihave H : kvrStorLogI (GF := GF) (kvrStorIface s) k dq es $$ [H]
  · unfold kvrStorLogI; iright; iexists s, ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

theorem kvrStorEnd_to (s ms : Loc) (γs : MemStorNames) (e : Nat) :
    ⊢ kvrStorRec (GF := GF) s ms γs -∗ storEnd (kvrStorIface s) e -∗ memEnd γs e := by
  iintro #Hreg H
  ihave H : kvrStorEndI (kvrStorIface s) e $$ [H]
  · iexact H
  unfold kvrStorEndI
  icases H with ⟨%s', %ms', %γs', %Hst, #Hreg', H⟩
  icases kvrStorRec_same (kvrStorIface s) s s' ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem kvrStorEnd_of (s ms : Loc) (γs : MemStorNames) (e : Nat) :
    ⊢ kvrStorRec (GF := GF) s ms γs -∗ memEnd γs e -∗ storEnd (kvrStorIface s) e := by
  iintro #Hreg H
  ihave H : kvrStorEndI (GF := GF) (kvrStorIface s) e $$ [H]
  · unfold kvrStorEndI; iexists s, ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

theorem kvrStorCompacted_to (s ms : Loc) (γs : MemStorNames) (c : Nat) :
    ⊢ kvrStorRec (GF := GF) s ms γs -∗ storCompacted (kvrStorIface s) c -∗ memCompacted γs c := by
  iintro #Hreg H
  ihave H : kvrStorCompactedI (kvrStorIface s) c $$ [H]
  · iexact H
  unfold kvrStorCompactedI
  icases H with (%H | ⟨%s', %ms', %γs', %Hst, #Hreg', #H⟩)
  · subst H; iapply memCompacted_zero
  icases kvrStorRec_same (kvrStorIface s) s s' ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem kvrStorCompacted_of (s ms : Loc) (γs : MemStorNames) (c : Nat) :
    ⊢ kvrStorRec (GF := GF) s ms γs -∗ memCompacted γs c -∗ storCompacted (kvrStorIface s) c := by
  iintro #Hreg #H
  ihave H : kvrStorCompactedI (GF := GF) (kvrStorIface s) c $$ []
  · unfold kvrStorCompactedI; iright; iexists s, ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

end conv

end stor

/-! ### The API's justifications -/

section just
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

/-- Node `id`'s justifications for its storage's `MemoryStorage` (raft's `memStorJ`, without its
registry): the stored snapshots valid, compaction within what node `id` applied or a snapshot it
handed out, a stored snapshot within what was delivered. -/
def kvrJ (γ : Cluster) (id : w64) : MemJust GF where
  SV := snapshotValid γ
  B k := iprop(nodeAppliedLb γ id k ∨ snapGiven γ id k)
  DL := storDL γ id
  SV_pers := fun sv => by infer_instance
  B_pers := fun k => by infer_instance
  B_timeless := fun k => by infer_instance
  DL_pers := fun i => by unfold storDL; infer_instance

end just

end kvreconf
end EtcdGrove
end Perennial
