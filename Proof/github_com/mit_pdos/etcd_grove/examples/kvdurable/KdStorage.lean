/-
Lean-first (no Rocq counterpart).

# The durable store's `Storage` and its `StorageModel` (2026-11-01, durability layer 4)

kvreconf's `KvrStorage.lean` at kvdurable's `*Storage` (the same wrapper: an embedded
`MemoryStorage` and the bootstrap `ConfState` `boot`, plus the replica's image of its file `img`,
`Image.lean`, which the wrappers of the storage changes change): the registry `kdStorRec s ms γs` keyed by the wrapper's
pointer, raft's vocabulary over it (`kdStorageModel`, a `def`, a local instance where used), and
the justifications `kdJ γ K` of the `MemoryStorage` of key `K` (raft's `memStorJ` without its
registry). Copied with renames; the proofs are kvreconf's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Base
public import Proof.go_etcd_io.raft.v3.MemstorageInstance
public import Proof.go_etcd_io.raft.v3.InvNodeRule
public import Spec.google_golang_org.protobuf.proto.CloneConfState

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The registry's ghost name (a ghost map from a wrapper's pointer to its `MemoryStorage` and that
storage's names). -/
class KdStor (GF : BundledGFunctors) where
  kdStorName : GName

/-- A registered wrapper's record: its `MemoryStorage` and that storage's names. -/
abbrev KdStorRecT := Loc × MemStorNamesRec

def kdStorRecOf (ms : Loc) (γs : MemStorNames) : KdStorRecT := (ms, γs.tuple)

theorem kdStorRecOf_inj (ms1 ms2 : Loc) (γs1 γs2 : MemStorNames) :
    kdStorRecOf ms1 γs1 = kdStorRecOf ms2 γs2 → ms1 = ms2 ∧ γs1 = γs2 := by
  intro h
  simp only [kdStorRecOf, Prod.mk.injEq] at h
  exact ⟨h.1, MemStorNames.rec_inj _ _ h.2⟩

def kdStorN : Namespace := nroot.@"kvdurable_storage"

section stor
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [KdStor GF]

/-- The raft `Storage` interface value of the store's storage `s` (`Cluster.config`'s
`Storage: st`, `st : *Storage`). -/
def kdStorIface (s : Loc) : Storage :=
  interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage.ty) #s

include sem in
theorem kdStorIface_inj (s1 s2 : Loc) : kdStorIface s1 = kdStorIface s2 → s1 = s2 := by
  intro h
  simp only [kdStorIface, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    true_and] at h
  exact go.intoVal_inj h

/-- The wrapper `s` holds the `MemoryStorage` `ms`, whose names are `γs` (persistent). -/
def kdStorRec (s ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(s.[github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage, go!"MemoryStorage"] ↦□ ms ∗
    s ↪[KdStor.kdStorName (GF := GF)]□ kdStorRecOf ms γs)

instance kdStorRec_persistent (s ms : Loc) (γs : MemStorNames) :
    Persistent (kdStorRec (GF := GF) s ms γs) := by
  unfold kdStorRec; infer_instance

theorem kdStorRec_agree (s ms1 ms2 : Loc) (γs1 γs2 : MemStorNames) :
    ⊢ kdStorRec (GF := GF) s ms1 γs1 -∗ kdStorRec s ms2 γs2 -∗ ⌜ms1 = ms2 ∧ γs1 = γs2⌝ := by
  unfold kdStorRec
  iintro ⟨-, #H1⟩ ⟨-, #H2⟩
  icases ghostMapElem_agree _ _ _ _ _ _ $$ H1 H2 with %H
  ipureintro; exact kdStorRecOf_inj _ _ _ _ H

/-- Two records of the same interface value agree. -/
theorem kdStorRec_same (st : Storage) (s1 s2 ms1 ms2 : Loc) (γs1 γs2 : MemStorNames)
    (h1 : st = kdStorIface s1) (h2 : st = kdStorIface s2) :
    ⊢ kdStorRec (GF := GF) s1 ms1 γs1 -∗ kdStorRec s2 ms2 γs2 -∗ ⌜ms1 = ms2 ∧ γs1 = γs2⌝ := by
  iintro #H1 #H2
  have := kdStorIface_inj (GF := GF) _ _ (h1.symm.trans h2)
  subst this
  iapply kdStorRec_agree s1 ms1 ms2 γs1 γs2 $$ H1 H2

/-- The wrapper's bootstrap conf state (persistent): its `boot` field, a read-only `ConfState`
holding `csm` (what `proto.CloneConfState.spec` reads). -/
def kdStorBoot (s bp : Loc) (csm : ConfStateM) : IProp GF :=
  iprop(s.[github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage, go!"boot"] ↦□ bp ∗
    ownCSM bp DFrac.discard csm)

instance kdStorBoot_persistent (s bp : Loc) (csm : ConfStateM) :
    Persistent (kdStorBoot (GF := GF) s bp csm) := by
  unfold kdStorBoot ownCSM; infer_instance

/-- The registry: its authority, and half of each registered wrapper's `MemoryStorage` field (so a
wrapper is registered once). -/
def kdStorInvBody : IProp GF :=
  iprop(∃ M : GMap Loc KdStorRecT, ghostMapAuth (KdStor.kdStorName (GF := GF)) 1 M ∗
    [∗map] s ↦ x ∈ M,
      s.[github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage, go!"MemoryStorage"]
        ↦{DFrac.own (1 : Qp).half} x.1)

def kdStorInv : IProp GF := inv kdStorN kdStorInvBody

instance kdStorInv_persistent : Persistent (kdStorInv (GF := GF)) := by
  unfold kdStorInv; infer_instance

instance kdStorInvBody_timeless : Timeless (kdStorInvBody (GF := GF)) := by
  unfold kdStorInvBody; infer_instance

/-- A pointer-valued location wholly owned has no other fraction. -/
theorem kdLoc_pointsto_excl (l : Loc) (v1 v2 : Loc) (q : Qp) :
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
theorem kdStor_register (s ms : Loc) (γs : MemStorNames) (E : CoPset) (HE : ↑kdStorN ⊆ E) :
    ⊢ kdStorInv (GF := GF) -∗
      s.[github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage, go!"MemoryStorage"] ↦ ms ={E}=∗
      kdStorRec s ms γs := by
  iintro #Hinv Hf
  unfold kdStorInv
  iinv Hinv with >Hi Hclose
  unfold kdStorInvBody
  icases Hi with ⟨%M, Ha, Hm⟩
  cases HM : M !! s with
  | some x =>
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun (s : Loc) (x : KdStorRecT) =>
      iprop(s.[github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage, go!"MemoryStorage"]
        ↦{DFrac.own (1 : Qp).half} x.1)) HM).1 $$ Hm
      with ⟨Hx, -⟩
    iexfalso
    iapply kdLoc_pointsto_excl $$ Hf Hx
  | none =>
    imod ghost_map_insert_persist s (kdStorRecOf ms γs) HM $$ Ha with ⟨Ha, #Hfrag⟩
    icases (typedPointsto_dfractional (GF := GF)
      (s.[github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage, go!"MemoryStorage"]) ms).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) |>.1 $$ [Hf] with ⟨Hf1, Hf2⟩
    · rw [DFrac.op_own, Qp.half_add_half]; iexact Hf
    imod (typedPointsto_dfractional (GF := GF) _ ms).dfractional_persist _ $$ Hf2 with #Hf2
    imod Hclose $$ [Ha Hm Hf1] with -
    · inext
      iexists M.insert s (kdStorRecOf ms γs)
      iframe Ha
      iapply (BigSepM.bigSepM_insert (Φ := fun (s : Loc) (x : KdStorRecT) =>
        iprop(s.[github_com.mit_pdos.etcd_grove.examples.kvdurable.Storage, go!"MemoryStorage"]
          ↦{DFrac.own (1 : Qp).half} x.1)) HM).2
      iframe Hm
      unfold kdStorRecOf
      iexact Hf1
    imodintro
    unfold kdStorRec
    iframe Hf2 Hfrag

/-! ### The vocabulary of a registered wrapper -/

/-- `storLog`: empty, or a registered wrapper's `MemoryStorage`'s range. -/
def kdStorLogI (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM) : IProp GF :=
  iprop(⌜es = []⌝ ∨ ∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kdStorIface s⌝ ∗
    kdStorRec s ms γs ∗ memLog γs k dq es)

/-- `storEnd`: a registered wrapper's `MemoryStorage`'s end. -/
def kdStorEndI (st : Storage) (e : Nat) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kdStorIface s⌝ ∗ kdStorRec s ms γs ∗
    memEnd γs e)

/-- `storCompacted`: `0`, or a registered wrapper's `MemoryStorage`'s compaction point. -/
def kdStorCompactedI (st : Storage) (c : Nat) : IProp GF :=
  iprop(⌜c = 0⌝ ∨ ∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kdStorIface s⌝ ∗
    kdStorRec s ms γs ∗ memCompacted γs c)

theorem kdStorLogI_app (st : Storage) (k : Nat) (dq : DFrac) (a b : List EntryM) :
    kdStorLogI (GF := GF) st k dq (a ++ b) ⊣⊢
      kdStorLogI st k dq a ∗ kdStorLogI st (k + a.length) dq b := by
  unfold kdStorLogI
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
    icases kdStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
    obtain ⟨rfl, rfl⟩ := Hsame
    iright
    iexists s, ms, γs
    iframe Hreg
    isplitr
    · ipureintro; exact Hst
    iapply (memLog_app γs k dq a b).2
    iframe

theorem kdStorLogI_frac (st : Storage) (k : Nat) (dq1 dq2 : DFrac) (es : List EntryM) :
    kdStorLogI (GF := GF) st k (dq1 • dq2) es ⊣⊢
      kdStorLogI st k dq1 es ∗ kdStorLogI st k dq2 es := by
  unfold kdStorLogI
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
    icases kdStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
    obtain ⟨rfl, rfl⟩ := Hsame
    iright
    iexists s, ms, γs
    iframe Hreg
    isplitr
    · ipureintro; exact Hst
    iapply (memLog_frac γs k dq1 dq2 es).2
    iframe

theorem kdStorLogI_valid (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM)
    (hne : es ≠ []) : kdStorLogI (GF := GF) st k dq es ⊢ ⌜✓ dq⌝ := by
  unfold kdStorLogI memLog
  iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H, -⟩)
  · exact absurd H hne
  obtain ⟨e, es', rfl⟩ : ∃ e es', es = e :: es' := List.exists_cons_of_ne_nil hne
  simp only [memLogL]
  icases H with ⟨H1, -⟩
  iapply ghostMapElem_valid $$ H1

/-- Two ranges of one map agree where they overlap (raft's `memLogL_agree`, which is stated
under `[MemStorReg GF]`, not in scope here). -/
theorem kdLogL_agree (γ : GName) (k1 k2 : Nat) (dq1 dq2 : DFrac) (es1 es2 : List EntryM) :
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

theorem kdStorLogI_agree (st : Storage) (k1 k2 : Nat) (dq1 dq2 : DFrac) (es1 es2 : List EntryM) :
    kdStorLogI (GF := GF) st k1 dq1 es1 ∗ kdStorLogI st k2 dq2 es2 ⊢ ⌜LogAgree k1 es1 k2 es2⌝ := by
  unfold kdStorLogI
  iintro ⟨H1, H2⟩
  icases H1 with (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H1⟩)
  · subst H; ipureintro; intro i e1 e2 _ _ h; simp at h
  icases H2 with (%H | ⟨%s', %ms', %γs', %Hst', #Hreg', H2⟩)
  · subst H; ipureintro; intro i e1 e2 _ _ _ h; simp at h
  icases kdStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  unfold memLog
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  iapply kdLogL_agree γs.log k1 k2 dq1 dq2 es1 es2
  iframe

theorem kdStorLogI_persist (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM) :
    kdStorLogI (GF := GF) st k dq es ⊢ |==> kdStorLogI st k DFrac.discard es := by
  unfold kdStorLogI
  iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H⟩)
  · imodintro; ileft; ipureintro; exact H
  imod memLog_persist γs k dq es $$ H with H
  imodintro
  iright; iexists s, ms, γs; iframe Hreg H; ipureintro; exact Hst

theorem kdStorEndI_excl (st : Storage) (e e' : Nat) :
    kdStorEndI (GF := GF) st e ∗ kdStorEndI st e' ⊢ False := by
  unfold kdStorEndI
  iintro ⟨⟨%s, %ms, %γs, %Hst, #Hreg, H1⟩, ⟨%s', %ms', %γs', %Hst', #Hreg', H2⟩⟩
  icases kdStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iapply memEnd_excl γs e e'
  iframe

theorem kdStorCompactedI_mono (st : Storage) (c c' : Nat) (h : c' ≤ c) :
    kdStorCompactedI (GF := GF) st c ⊢ kdStorCompactedI st c' := by
  unfold kdStorCompactedI
  iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, #H⟩)
  · ileft; ipureintro; omega
  iright; iexists s, ms, γs; iframe Hreg
  isplitr
  · ipureintro; exact Hst
  iapply memCompacted_mono γs c c' h $$ H

/-- **The store's storage model**: every `Storage` raft sees is a registered wrapper. A `def`, made
an instance locally by the files that need it (`attribute [local instance] kdStorageModel`). -/
@[instance_reducible]
def kdStorageModel : StorageModel GF where
  storLog := kdStorLogI
  storEnd := kdStorEndI
  storCompacted := kdStorCompactedI
  storLog_app := kdStorLogI_app
  storLog_frac := kdStorLogI_frac
  storLog_valid := kdStorLogI_valid
  storLog_agree := kdStorLogI_agree
  storLog_persist := kdStorLogI_persist
  storLog_persistent := fun st k es => by unfold kdStorLogI; infer_instance
  storLog_nil := fun st k dq => by unfold kdStorLogI; iintro; ileft; ipureintro; rfl
  storEnd_excl := kdStorEndI_excl
  storCompacted_persistent := fun st c => by unfold kdStorCompactedI; infer_instance
  storCompacted_zero := fun st => by unfold kdStorCompactedI; iintro; ileft; ipureintro; rfl
  storCompacted_mono := kdStorCompactedI_mono

/-! ### The conversions, under the wrapper's record -/

section conv
attribute [local instance] kdStorageModel

theorem kdStorLog_to (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ kdStorRec (GF := GF) s ms γs -∗ storLog (kdStorIface s) k dq es -∗ memLog γs k dq es := by
  iintro #Hreg H
  ihave H : kdStorLogI (kdStorIface s) k dq es $$ [H]
  · iexact H
  unfold kdStorLogI
  icases H with (%H | ⟨%s', %ms', %γs', %Hst, #Hreg', H⟩)
  · subst H; iapply memLog_nil
  icases kdStorRec_same (kdStorIface s) s s' ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem kdStorLog_of (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ kdStorRec (GF := GF) s ms γs -∗ memLog γs k dq es -∗ storLog (kdStorIface s) k dq es := by
  iintro #Hreg H
  ihave H : kdStorLogI (GF := GF) (kdStorIface s) k dq es $$ [H]
  · unfold kdStorLogI; iright; iexists s, ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

theorem kdStorEnd_to (s ms : Loc) (γs : MemStorNames) (e : Nat) :
    ⊢ kdStorRec (GF := GF) s ms γs -∗ storEnd (kdStorIface s) e -∗ memEnd γs e := by
  iintro #Hreg H
  ihave H : kdStorEndI (kdStorIface s) e $$ [H]
  · iexact H
  unfold kdStorEndI
  icases H with ⟨%s', %ms', %γs', %Hst, #Hreg', H⟩
  icases kdStorRec_same (kdStorIface s) s s' ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem kdStorEnd_of (s ms : Loc) (γs : MemStorNames) (e : Nat) :
    ⊢ kdStorRec (GF := GF) s ms γs -∗ memEnd γs e -∗ storEnd (kdStorIface s) e := by
  iintro #Hreg H
  ihave H : kdStorEndI (GF := GF) (kdStorIface s) e $$ [H]
  · unfold kdStorEndI; iexists s, ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

theorem kdStorCompacted_to (s ms : Loc) (γs : MemStorNames) (c : Nat) :
    ⊢ kdStorRec (GF := GF) s ms γs -∗ storCompacted (kdStorIface s) c -∗ memCompacted γs c := by
  iintro #Hreg H
  ihave H : kdStorCompactedI (kdStorIface s) c $$ [H]
  · iexact H
  unfold kdStorCompactedI
  icases H with (%H | ⟨%s', %ms', %γs', %Hst, #Hreg', #H⟩)
  · subst H; iapply memCompacted_zero
  icases kdStorRec_same (kdStorIface s) s s' ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem kdStorCompacted_of (s ms : Loc) (γs : MemStorNames) (c : Nat) :
    ⊢ kdStorRec (GF := GF) s ms γs -∗ memCompacted γs c -∗ storCompacted (kdStorIface s) c := by
  iintro #Hreg #H
  ihave H : kdStorCompactedI (GF := GF) (kdStorIface s) c $$ []
  · unfold kdStorCompactedI; iright; iexists s, ms, γs; iframe Hreg H; ipureintro; rfl
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

/-- The justifications for the `MemoryStorage` of key `K` (raft's `memStorJ`, without its registry;
2026-11-01, durability stage I-4: keyed by the storage's key, `snapGiven` merged into
`nodeAppliedLb`, `storDL` now `nodeCommitLb`). -/
def kdJ (γ : Cluster) (K : GName) : MemJust GF where
  SV := snapshotValid γ
  B k := nodeAppliedLb γ K k
  DL := nodeCommitLb γ K
  SV_pers := fun sv => by infer_instance
  B_pers := fun k => by infer_instance
  B_timeless := fun k => by infer_instance
  DL_pers := fun i => by infer_instance

end just

end kvdurable
end EtcdGrove
end Perennial
