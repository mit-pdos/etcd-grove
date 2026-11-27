/-
Lean-first (no Rocq counterpart). #33 S4, P-harness.

# The harness's storage and raft's `StorageModel` over it

kvdurable's `KdStorage.lean` (itself kvreconf's `KvrStorage.lean`) at the harness's `bootStorage`, copied
with renames: the registry `antStorRec s ms γs` keyed by the wrapper's pointer (its `ms` field, half
persistent, half in the registry's invariant), raft's vocabulary over it (`antStorageModel`, a `def`,
a local instance where used) and the conversions between it and the `MemoryStorage`'s `memLog`/`memEnd`.

The harness's specs keep raft's `StorageModel` abstract; a node's state (`nodeOwn`) instead carries
the **bridge** `antStorBridge st γs`: raft's `storLog`/`storEnd` of the node's storage `st` are its
`MemoryStorage`'s `memLog`/`memEnd` (what `drain`'s `Append` needs of `Ready`'s `appendRight` and
gives back to `Advance`). Under `antStorageModel` a registered wrapper's interface has the bridge
(`antStor_bridge`), which is how `RunCluster` builds it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessBase
public import Proof.go_etcd_io.raft.v3.MemstorageInstance
public import Proof.go_etcd_io.raft.v3.InvNodeRule

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The registry's ghost name (a ghost map from a wrapper's pointer to its `MemoryStorage` and that
storage's names). -/
class AntStor (GF : BundledGFunctors) where
  antStorName : GName

/-- A registered wrapper's record: its `MemoryStorage` and that storage's names. -/
abbrev AntStorRecT := Loc × MemStorNamesRec

def antStorRecOf (ms : Loc) (γs : MemStorNames) : AntStorRecT := (ms, γs.tuple)

theorem antStorRecOf_inj (ms1 ms2 : Loc) (γs1 γs2 : MemStorNames) :
    antStorRecOf ms1 γs1 = antStorRecOf ms2 γs2 → ms1 = ms2 ∧ γs1 = γs2 := by
  intro h
  simp only [antStorRecOf, Prod.mk.injEq] at h
  exact ⟨h.1, MemStorNames.rec_inj _ _ h.2⟩

def antStorN : Namespace := nroot.@"antithesis_storage"

section stor
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [AntStor GF]

/-- The raft `Storage` interface value of the store's storage `s` (`NewCluster`'s
`Storage: &bootStorage{…}`). -/
def antStorIface (s : Loc) : Storage :=
  interface.ok ⟨go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #s⟩

include sem in
theorem antStorIface_inj (s1 s2 : Loc) : antStorIface s1 = antStorIface s2 → s1 = s2 := by
  intro h
  simp only [antStorIface, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    true_and] at h
  exact go.intoVal_inj h

/-- The wrapper `s` holds the `MemoryStorage` `ms`, whose names are `γs` (persistent). The storage is
unsized (`γs.sz = false`): the harness bounds no proposed data (`nodeRaft`'s `maxData = none`). -/
def antStorRec (s ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(s.[H.bootStorage, go!"ms"] ↦□ ms ∗
    s ↪[AntStor.antStorName (GF := GF)]□ antStorRecOf ms γs ∗ ⌜γs.sz = false⌝)

instance antStorRec_persistent (s ms : Loc) (γs : MemStorNames) :
    Persistent (antStorRec (GF := GF) s ms γs) := by
  unfold antStorRec; infer_instance

theorem antStorRec_agree (s ms1 ms2 : Loc) (γs1 γs2 : MemStorNames) :
    ⊢ antStorRec (GF := GF) s ms1 γs1 -∗ antStorRec s ms2 γs2 -∗ ⌜ms1 = ms2 ∧ γs1 = γs2⌝ := by
  unfold antStorRec
  iintro ⟨-, #H1, -⟩ ⟨-, #H2, -⟩
  icases ghostMapElem_agree _ _ _ _ _ _ $$ H1 H2 with %H
  ipureintro; exact antStorRecOf_inj _ _ _ _ H

/-- Two records of the same interface value agree. -/
theorem antStorRec_same (st : Storage) (s1 s2 ms1 ms2 : Loc) (γs1 γs2 : MemStorNames)
    (h1 : st = antStorIface s1) (h2 : st = antStorIface s2) :
    ⊢ antStorRec (GF := GF) s1 ms1 γs1 -∗ antStorRec s2 ms2 γs2 -∗ ⌜ms1 = ms2 ∧ γs1 = γs2⌝ := by
  iintro #H1 #H2
  have := antStorIface_inj (GF := GF) _ _ (h1.symm.trans h2)
  subst this
  iapply antStorRec_agree s1 ms1 ms2 γs1 γs2 $$ H1 H2

/-- The registry: its authority, and half of each registered wrapper's `MemoryStorage` field (so a
wrapper is registered once). -/
def antStorInvBody : IProp GF :=
  iprop(∃ M : GMap Loc AntStorRecT, ghostMapAuth (AntStor.antStorName (GF := GF)) 1 M ∗
    [∗map] s ↦ x ∈ M,
      s.[H.bootStorage, go!"ms"]
        ↦{DFrac.own (1 : Qp).half} x.1)

def antStorInv : IProp GF := inv antStorN antStorInvBody

instance antStorInv_persistent : Persistent (antStorInv (GF := GF)) := by
  unfold antStorInv; infer_instance

instance antStorInvBody_timeless : Timeless (antStorInvBody (GF := GF)) := by
  unfold antStorInvBody; infer_instance

/-- A pointer-valued location wholly owned has no other fraction. -/
theorem antLoc_pointsto_excl (l : Loc) (v1 v2 : Loc) (q : Qp) :
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
theorem antStor_register (s ms : Loc) (γs : MemStorNames) (E : CoPset) (HE : ↑antStorN ⊆ E)
    (hsz : γs.sz = false) :
    ⊢ antStorInv (GF := GF) -∗
      s.[H.bootStorage, go!"ms"] ↦ ms ={E}=∗
      antStorRec s ms γs := by
  iintro #Hinv Hf
  unfold antStorInv
  iinv Hinv with >Hi Hclose
  unfold antStorInvBody
  icases Hi with ⟨%M, Ha, Hm⟩
  cases HM : M !! s with
  | some x =>
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun (s : Loc) (x : AntStorRecT) =>
      iprop(s.[H.bootStorage, go!"ms"]
        ↦{DFrac.own (1 : Qp).half} x.1)) HM).1 $$ Hm
      with ⟨Hx, -⟩
    iexfalso
    iapply antLoc_pointsto_excl $$ Hf Hx
  | none =>
    imod ghost_map_insert_persist s (antStorRecOf ms γs) HM $$ Ha with ⟨Ha, #Hfrag⟩
    icases (typedPointsto_dfractional (GF := GF)
      (s.[H.bootStorage, go!"ms"]) ms).dfractional
      (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half) |>.1 $$ [Hf] with ⟨Hf1, Hf2⟩
    · rw [DFrac.op_own, Qp.half_add_half]; iexact Hf
    imod (typedPointsto_dfractional (GF := GF) _ ms).dfractional_persist _ $$ Hf2 with #Hf2
    imod Hclose $$ [Ha Hm Hf1] with -
    · inext
      iexists M.insert s (antStorRecOf ms γs)
      iframe Ha
      iapply (BigSepM.bigSepM_insert (Φ := fun (s : Loc) (x : AntStorRecT) =>
        iprop(s.[H.bootStorage, go!"ms"]
          ↦{DFrac.own (1 : Qp).half} x.1)) HM).2
      iframe Hm
      unfold antStorRecOf
      iexact Hf1
    imodintro
    unfold antStorRec
    iframe Hf2 Hfrag
    ipureintro; exact hsz

/-! ### The vocabulary of a registered wrapper -/

/-- `storLog`: empty, or a registered wrapper's `MemoryStorage`'s range. -/
def antStorLogI (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM) : IProp GF :=
  iprop(⌜es = []⌝ ∨ ∃ (s ms : Loc) (γs : MemStorNames), ⌜st = antStorIface s⌝ ∗
    antStorRec s ms γs ∗ memLog γs k dq es)

/-- `storEnd`: a registered wrapper's `MemoryStorage`'s end. -/
def antStorEndI (st : Storage) (e : Nat) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = antStorIface s⌝ ∗ antStorRec s ms γs ∗
    memEnd γs e)

/-- `storCompacted`: `0`, or a registered wrapper's `MemoryStorage`'s compaction point. -/
def antStorCompactedI (st : Storage) (c : Nat) : IProp GF :=
  iprop(⌜c = 0⌝ ∨ ∃ (s ms : Loc) (γs : MemStorNames), ⌜st = antStorIface s⌝ ∗
    antStorRec s ms γs ∗ memCompacted γs c)

theorem antStorLogI_app (st : Storage) (k : Nat) (dq : DFrac) (a b : List EntryM) :
    antStorLogI (GF := GF) st k dq (a ++ b) ⊣⊢
      antStorLogI st k dq a ∗ antStorLogI st (k + a.length) dq b := by
  unfold antStorLogI
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
    icases antStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
    obtain ⟨rfl, rfl⟩ := Hsame
    iright
    iexists s, ms, γs
    iframe Hreg
    isplitr
    · ipureintro; exact Hst
    iapply (memLog_app γs k dq a b).2
    iframe

theorem antStorLogI_frac (st : Storage) (k : Nat) (dq1 dq2 : DFrac) (es : List EntryM) :
    antStorLogI (GF := GF) st k (dq1 • dq2) es ⊣⊢
      antStorLogI st k dq1 es ∗ antStorLogI st k dq2 es := by
  unfold antStorLogI
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
    icases antStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
    obtain ⟨rfl, rfl⟩ := Hsame
    iright
    iexists s, ms, γs
    iframe Hreg
    isplitr
    · ipureintro; exact Hst
    iapply (memLog_frac γs k dq1 dq2 es).2
    iframe

theorem antStorLogI_valid (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM)
    (hne : es ≠ []) : antStorLogI (GF := GF) st k dq es ⊢ ⌜✓ dq⌝ := by
  unfold antStorLogI memLog
  iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H, -⟩)
  · exact absurd H hne
  obtain ⟨e, es', rfl⟩ : ∃ e es', es = e :: es' := List.exists_cons_of_ne_nil hne
  simp only [memLogL]
  icases H with ⟨H1, -⟩
  iapply ghostMapElem_valid $$ H1

/-- Two ranges of one map agree where they overlap (raft's `memLogL_agree`, which is stated
under `[MemStorReg GF]`, not in scope here). -/
theorem antLogL_agree (γ : GName) (k1 k2 : Nat) (dq1 dq2 : DFrac) (es1 es2 : List EntryM) :
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

theorem antStorLogI_agree (st : Storage) (k1 k2 : Nat) (dq1 dq2 : DFrac) (es1 es2 : List EntryM) :
    antStorLogI (GF := GF) st k1 dq1 es1 ∗ antStorLogI st k2 dq2 es2 ⊢ ⌜LogAgree k1 es1 k2 es2⌝ := by
  unfold antStorLogI
  iintro ⟨H1, H2⟩
  icases H1 with (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H1⟩)
  · subst H; ipureintro; intro i e1 e2 _ _ h; simp at h
  icases H2 with (%H | ⟨%s', %ms', %γs', %Hst', #Hreg', H2⟩)
  · subst H; ipureintro; intro i e1 e2 _ _ _ h; simp at h
  icases antStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  unfold memLog
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  iapply antLogL_agree γs.log k1 k2 dq1 dq2 es1 es2
  iframe

theorem antStorLogI_persist (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM) :
    antStorLogI (GF := GF) st k dq es ⊢ |==> antStorLogI st k DFrac.discard es := by
  unfold antStorLogI
  iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, H⟩)
  · imodintro; ileft; ipureintro; exact H
  imod memLog_persist γs k dq es $$ H with H
  imodintro
  iright; iexists s, ms, γs; iframe Hreg H; ipureintro; exact Hst

theorem antStorEndI_excl (st : Storage) (e e' : Nat) :
    antStorEndI (GF := GF) st e ∗ antStorEndI st e' ⊢ False := by
  unfold antStorEndI
  iintro ⟨⟨%s, %ms, %γs, %Hst, #Hreg, H1⟩, ⟨%s', %ms', %γs', %Hst', #Hreg', H2⟩⟩
  icases antStorRec_same st s s' ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iapply memEnd_excl γs e e'
  iframe

theorem antStorCompactedI_mono (st : Storage) (c c' : Nat) (h : c' ≤ c) :
    antStorCompactedI (GF := GF) st c ⊢ antStorCompactedI st c' := by
  unfold antStorCompactedI
  iintro (%H | ⟨%s, %ms, %γs, %Hst, #Hreg, #H⟩)
  · ileft; ipureintro; omega
  iright; iexists s, ms, γs; iframe Hreg
  isplitr
  · ipureintro; exact Hst
  iapply memCompacted_mono γs c c' h $$ H

/-- **The store's storage model**: every `Storage` raft sees is a registered wrapper. A `def`, made
an instance locally by the files that need it (`attribute [local instance] antStorageModel`). -/
@[instance_reducible]
def antStorageModel : StorageModel GF where
  storLog := antStorLogI
  storEnd := antStorEndI
  storCompacted := antStorCompactedI
  storLog_app := antStorLogI_app
  storLog_frac := antStorLogI_frac
  storLog_valid := antStorLogI_valid
  storLog_agree := antStorLogI_agree
  storLog_persist := antStorLogI_persist
  storLog_persistent := fun st k es => by unfold antStorLogI; infer_instance
  storLog_nil := fun st k dq => by unfold antStorLogI; iintro; ileft; ipureintro; rfl
  storEnd_excl := antStorEndI_excl
  storCompacted_persistent := fun st c => by unfold antStorCompactedI; infer_instance
  storCompacted_zero := fun st => by unfold antStorCompactedI; iintro; ileft; ipureintro; rfl
  storCompacted_mono := antStorCompactedI_mono

/-! ### The conversions, under the wrapper's record -/

section conv
attribute [local instance] antStorageModel

theorem antStorLog_to (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ antStorRec (GF := GF) s ms γs -∗ storLog (antStorIface s) k dq es -∗ memLog γs k dq es := by
  iintro #Hreg H
  ihave H : antStorLogI (antStorIface s) k dq es $$ [H]
  · iexact H
  unfold antStorLogI
  icases H with (%H | ⟨%s', %ms', %γs', %Hst, #Hreg', H⟩)
  · subst H; iapply memLog_nil
  icases antStorRec_same (antStorIface s) s s' ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem antStorLog_of (s ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ antStorRec (GF := GF) s ms γs -∗ memLog γs k dq es -∗ storLog (antStorIface s) k dq es := by
  iintro #Hreg H
  ihave H : antStorLogI (GF := GF) (antStorIface s) k dq es $$ [H]
  · unfold antStorLogI; iright; iexists s, ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

theorem antStorEnd_to (s ms : Loc) (γs : MemStorNames) (e : Nat) :
    ⊢ antStorRec (GF := GF) s ms γs -∗ storEnd (antStorIface s) e -∗ memEnd γs e := by
  iintro #Hreg H
  ihave H : antStorEndI (antStorIface s) e $$ [H]
  · iexact H
  unfold antStorEndI
  icases H with ⟨%s', %ms', %γs', %Hst, #Hreg', H⟩
  icases antStorRec_same (antStorIface s) s s' ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem antStorEnd_of (s ms : Loc) (γs : MemStorNames) (e : Nat) :
    ⊢ antStorRec (GF := GF) s ms γs -∗ memEnd γs e -∗ storEnd (antStorIface s) e := by
  iintro #Hreg H
  ihave H : antStorEndI (GF := GF) (antStorIface s) e $$ [H]
  · unfold antStorEndI; iexists s, ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

theorem antStorCompacted_to (s ms : Loc) (γs : MemStorNames) (c : Nat) :
    ⊢ antStorRec (GF := GF) s ms γs -∗ storCompacted (antStorIface s) c -∗ memCompacted γs c := by
  iintro #Hreg H
  ihave H : antStorCompactedI (antStorIface s) c $$ [H]
  · iexact H
  unfold antStorCompactedI
  icases H with (%H | ⟨%s', %ms', %γs', %Hst, #Hreg', #H⟩)
  · subst H; iapply memCompacted_zero
  icases antStorRec_same (antStorIface s) s s' ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem antStorCompacted_of (s ms : Loc) (γs : MemStorNames) (c : Nat) :
    ⊢ antStorRec (GF := GF) s ms γs -∗ memCompacted γs c -∗ storCompacted (antStorIface s) c := by
  iintro #Hreg #H
  ihave H : antStorCompactedI (GF := GF) (antStorIface s) c $$ []
  · unfold antStorCompactedI; iright; iexists s, ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

end conv

end stor

/-! ### The bridge (over any `StorageModel`) -/

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]

/-- **The storage `st` is the `MemoryStorage` of names `γs`** (persistent): raft's `storLog` and
`storEnd` of `st` are the `MemoryStorage`'s `memLog` and `memEnd`. -/
def antStorBridge (st : Storage) (γs : MemStorNames) : IProp GF :=
  iprop(□ (∀ (k : Nat) (dq : DFrac) (es : List EntryM), storLog st k dq es ∗-∗ memLog γs k dq es) ∗
    □ (∀ e : Nat, storEnd st e ∗-∗ memEnd γs e))

instance antStorBridge_persistent (st : Storage) (γs : MemStorNames) :
    Persistent (antStorBridge (GF := GF) st γs) := by
  unfold antStorBridge; infer_instance

theorem antStorBridge_log_to (st : Storage) (γs : MemStorNames) (k : Nat) (dq : DFrac)
    (es : List EntryM) :
    ⊢ antStorBridge (GF := GF) st γs -∗ storLog st k dq es -∗ memLog γs k dq es := by
  unfold antStorBridge
  iintro ⟨#Hl, -⟩ H
  iapply Hl $$ H

theorem antStorBridge_log_of (st : Storage) (γs : MemStorNames) (k : Nat) (dq : DFrac)
    (es : List EntryM) :
    ⊢ antStorBridge (GF := GF) st γs -∗ memLog γs k dq es -∗ storLog st k dq es := by
  unfold antStorBridge
  iintro ⟨#Hl, -⟩ H
  iapply Hl $$ H

theorem antStorBridge_end_to (st : Storage) (γs : MemStorNames) (e : Nat) :
    ⊢ antStorBridge (GF := GF) st γs -∗ storEnd st e -∗ memEnd γs e := by
  unfold antStorBridge
  iintro ⟨-, #He⟩ H
  iapply He $$ H

theorem antStorBridge_end_of (st : Storage) (γs : MemStorNames) (e : Nat) :
    ⊢ antStorBridge (GF := GF) st γs -∗ memEnd γs e -∗ storEnd st e := by
  unfold antStorBridge
  iintro ⟨-, #He⟩ H
  iapply He $$ H

end bridge

section nodeStor
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]

/-- **A node's storage** (`nodeOwn`'s): the `bootStorage` `si` raft reads (its fields: the
`MemoryStorage` `ms`, the run's initial voters `vs`), the `MemoryStorage`'s lock and the hard state `hs` written
last (`memStorMeta`), the bridge from raft's view of `si` to the `MemoryStorage`'s names `γs`, and
the storage unsized (`Append` takes `Ready`'s `entsROz false`). -/
def nodeStor (si ms : Loc) (vs : List w64) (hs : HardStateM) : IProp GF :=
  iprop(bootStorRec si ms vs ∗ ∃ γs : MemStorNames, memStorLock ms γs ∗
    memStorMeta ms γs hs ∗
    antStorBridge (interface.ok ⟨go.GoType.PointerType
      github_com.mit_pdos.etcd_grove.examples.raft.antithesis.bootStorage.ty, #si⟩) γs ∗
    ⌜γs.sz = false⌝)

end nodeStor

section bridge_reg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [AntStor GF]
attribute [local instance] antStorageModel

/-- **A registered wrapper's interface has the bridge** (under `antStorageModel`). -/
theorem antStor_bridge (s ms : Loc) (γs : MemStorNames) :
    ⊢ antStorRec (GF := GF) s ms γs -∗ antStorBridge (antStorIface s) γs := by
  iintro #Hreg
  unfold antStorBridge
  isplitl []
  · imodintro
    iintro %k %dq %es
    isplit
    · iintro H; iapply antStorLog_to s ms γs k dq es $$ Hreg H
    · iintro H; iapply antStorLog_of s ms γs k dq es $$ Hreg H
  · imodintro
    iintro %e
    isplit
    · iintro H; iapply antStorEnd_to s ms γs e $$ Hreg H
    · iintro H; iapply antStorEnd_of s ms γs e $$ Hreg H

/-- The registry's record gives the `bootStorage`'s `ms` field (with `bootStorRec`'s voters). -/
theorem antStorRec_ms (s ms : Loc) (γs : MemStorNames) :
    antStorRec (GF := GF) s ms γs ⊢ s.[H.bootStorage, go!"ms"] ↦□ ms := by
  unfold antStorRec
  iintro ⟨#H, -⟩
  iexact H

end bridge_reg

end AntHarness
end EtcdGrove
end Perennial
