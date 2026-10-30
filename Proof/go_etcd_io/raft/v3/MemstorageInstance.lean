/-
### The `StorageModel` instance for `*MemoryStorage`, and the contract (U8 v2 step 3, 2026-10-29)

`memStorageModel`: the range vocabulary (`InvStorage.lean`'s class) for an application whose
`Storage`s are bare `MemoryStorage`s. The instance recovers a storage's ghost names from its pointer
through a **registry**, a ghost map from the pointer to the names (`memStorReg ms γs`, persistent),
whose name is the class `MemStorReg` (allocated by the application before the run) and whose
authority is the application's (`memStorReg_register`: the pointer must be absent, which the
application knows of the map it holds). Then `storLog (memStorIface ms)`, `storEnd …`,
`storCompacted …` are the storage's `memLog`, `memEnd`, `memCompacted` (`memStorLog_iff`, ...); a
range or the compaction point `0` holds of any storage (`storLog_nil`, `storCompacted_zero`).

**The contract law** (`memStorage_isStorageP`): `memStorInvP ms γs J ∗ memStorReg ms γs ⊢
isStorageP J.SV (memBnd J) J.DL (memStorIface ms)`, from the five read methods' specs (hypotheses,
as a proof takes its callees' specs; `Link.lean` passes them). Step 4 instantiates `J` to the API's
names: the approved `memStorInv ms γs γ id ∗ memStorReg ms γs ⊢ isStorage γ id st`.
-/
module

public import Spec.go_etcd_io.raft.v3.MemoryStorage__LastIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__FirstIndex
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Term
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Entries
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The registry's ghost name: a class, so that `memStorageModel` can be an instance. -/
class MemStorReg (GF : BundledGFunctors) where
  memStorRegName : GName

/-- A storage's names, as the registry records them. -/
abbrev MemStorNamesRec := GName × GName × GName × GName × GName × GName × GName × GName × GName × GName

def MemStorNames.tuple (γs : MemStorNames) : MemStorNamesRec :=
  (γs.log, γs.en, γs.ek, γs.cp, γs.jc, γs.sx, γs.lk, γs.hk, γs.sl, γs.pr)

theorem MemStorNames.rec_inj (γs1 γs2 : MemStorNames) (h : γs1.tuple = γs2.tuple) : γs1 = γs2 := by
  cases γs1; cases γs2
  simp only [MemStorNames.tuple, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

section model
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [MemStorReg GF]

/-- The registry's authority: the storages registered so far, with their names. -/
def memStorRegAuth (M : GMap Loc MemStorNamesRec) : IProp GF :=
  ghostMapAuth (MemStorReg.memStorRegName (GF := GF)) 1 M

/-- The `MemoryStorage` `ms` has the names `γs` (persistent). -/
def memStorReg (ms : Loc) (γs : MemStorNames) : IProp GF :=
  ms ↪[MemStorReg.memStorRegName (GF := GF)]□ γs.tuple

instance memStorReg_persistent (ms : Loc) (γs : MemStorNames) :
    Persistent (memStorReg (GF := GF) ms γs) := by
  unfold memStorReg; infer_instance

theorem memStorReg_agree (ms : Loc) (γs1 γs2 : MemStorNames) :
    ⊢ memStorReg (GF := GF) ms γs1 -∗ memStorReg ms γs2 -∗ ⌜γs1 = γs2⌝ := by
  unfold memStorReg
  iintro #H1 #H2
  icases ghostMapElem_agree _ _ _ _ _ _ $$ H1 H2 with %H
  ipureintro; exact MemStorNames.rec_inj _ _ H

/-- Register a storage (the application, holding the registry's authority). -/
theorem memStorReg_register (M : GMap Loc MemStorNamesRec) (ms : Loc) (γs : MemStorNames)
    (h : M.lookup ms = none) :
    ⊢ memStorRegAuth (GF := GF) M ==∗ memStorRegAuth (M.insert ms γs.tuple) ∗ memStorReg ms γs := by
  unfold memStorRegAuth memStorReg
  iintro Ha
  iapply ghost_map_insert_persist ms γs.tuple h $$ Ha

/-- The raft `Storage` interface value holding the `*MemoryStorage` `ms`. -/
def memStorIface (ms : Loc) : Storage :=
  interface.mkOk (go.GoType.PointerType MemoryStorage.ty) #ms

include sem in
theorem memStorIface_inj (ms1 ms2 : Loc) : memStorIface ms1 = memStorIface ms2 → ms1 = ms2 := by
  intro h
  simp only [memStorIface, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    true_and] at h
  exact go.intoVal_inj h

/-! ### The vocabulary of a registered storage -/

/-- `storLog`: empty, or a registered storage's range. -/
def memStorLogI (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM) : IProp GF :=
  iprop(⌜es = []⌝ ∨ ∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    memLog γs k dq es)

/-- `storEnd`: a registered storage's end. -/
def memStorEndI (st : Storage) (e : Nat) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗ memEnd γs e)

/-- `storCompacted`: `0`, or a registered storage's compaction point. -/
def memStorCompactedI (st : Storage) (c : Nat) : IProp GF :=
  iprop(⌜c = 0⌝ ∨ ∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    memCompacted γs c)

/-- Two registrations of the same interface value have the same storage and names. -/
theorem memStorReg_same (st : Storage) (ms1 ms2 : Loc) (γs1 γs2 : MemStorNames)
    (h1 : st = memStorIface ms1) (h2 : st = memStorIface ms2) :
    ⊢ memStorReg (GF := GF) ms1 γs1 -∗ memStorReg ms2 γs2 -∗ ⌜ms1 = ms2 ∧ γs1 = γs2⌝ := by
  iintro #H1 #H2
  have := memStorIface_inj (GF := GF) _ _ (h1.symm.trans h2)
  subst this
  icases memStorReg_agree ms1 γs1 γs2 $$ H1 H2 with %H
  ipureintro; exact ⟨rfl, H⟩

theorem memStorLogI_app (st : Storage) (k : Nat) (dq : DFrac) (a b : List EntryM) :
    memStorLogI (GF := GF) st k dq (a ++ b) ⊣⊢
      memStorLogI st k dq a ∗ memStorLogI st (k + a.length) dq b := by
  unfold memStorLogI
  constructor
  · iintro (%H | ⟨%ms, %γs, %Hst, #Hreg, H⟩)
    · simp only [List.append_eq_nil_iff] at H
      isplitl [] <;> ileft <;> ipureintro
      · exact H.1
      · exact H.2
    icases (memLog_app γs k dq a b).1 $$ H with ⟨Ha, Hb⟩
    isplitl [Ha]
    · iright; iexists ms, γs; iframe Hreg Ha; ipureintro; exact Hst
    · iright; iexists ms, γs; iframe Hreg Hb; ipureintro; exact Hst
  · iintro ⟨Ha, Hb⟩
    icases Ha with (%Ha | ⟨%ms, %γs, %Hst, #Hreg, Ha⟩)
    · subst Ha
      simp only [List.nil_append, List.length_nil, Nat.add_zero]
      iexact Hb
    icases Hb with (%Hb | ⟨%ms', %γs', %Hst', #Hreg', Hb⟩)
    · subst Hb
      simp only [List.append_nil]
      iright; iexists ms, γs; iframe Hreg Ha; ipureintro; exact Hst
    icases memStorReg_same st ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
    obtain ⟨rfl, rfl⟩ := Hsame
    iright
    iexists ms, γs
    iframe Hreg
    isplitr
    · ipureintro; exact Hst
    iapply (memLog_app γs k dq a b).2
    iframe

theorem memStorLogI_frac (st : Storage) (k : Nat) (dq1 dq2 : DFrac) (es : List EntryM) :
    memStorLogI (GF := GF) st k (dq1 • dq2) es ⊣⊢ memStorLogI st k dq1 es ∗ memStorLogI st k dq2 es := by
  unfold memStorLogI
  constructor
  · iintro (%H | ⟨%ms, %γs, %Hst, #Hreg, H⟩)
    · isplitl [] <;> ileft <;> ipureintro <;> exact H
    icases (memLog_frac γs k dq1 dq2 es).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iright; iexists ms, γs; iframe Hreg H1; ipureintro; exact Hst
    · iright; iexists ms, γs; iframe Hreg H2; ipureintro; exact Hst
  · iintro ⟨H1, H2⟩
    icases H1 with (%H | ⟨%ms, %γs, %Hst, #Hreg, H1⟩)
    · ileft; ipureintro; exact H
    icases H2 with (%H | ⟨%ms', %γs', %Hst', #Hreg', H2⟩)
    · ileft; ipureintro; exact H
    icases memStorReg_same st ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
    obtain ⟨rfl, rfl⟩ := Hsame
    iright
    iexists ms, γs
    iframe Hreg
    isplitr
    · ipureintro; exact Hst
    iapply (memLog_frac γs k dq1 dq2 es).2
    iframe

theorem memStorLogI_valid (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM) (hne : es ≠ []) :
    memStorLogI (GF := GF) st k dq es ⊢ ⌜✓ dq⌝ := by
  unfold memStorLogI memLog
  iintro (%H | ⟨%ms, %γs, %Hst, #Hreg, H, -⟩)
  · exact absurd H hne
  obtain ⟨e, es', rfl⟩ : ∃ e es', es = e :: es' := List.exists_cons_of_ne_nil hne
  simp only [memLogL]
  icases H with ⟨H1, -⟩
  iapply ghostMapElem_valid $$ H1

/-- Two ranges of one map agree where they overlap. -/
theorem memLogL_agree (γ : GName) (k1 k2 : Nat) (dq1 dq2 : DFrac) (es1 es2 : List EntryM) :
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

theorem memStorLogI_agree (st : Storage) (k1 k2 : Nat) (dq1 dq2 : DFrac) (es1 es2 : List EntryM) :
    memStorLogI (GF := GF) st k1 dq1 es1 ∗ memStorLogI st k2 dq2 es2 ⊢ ⌜LogAgree k1 es1 k2 es2⌝ := by
  unfold memStorLogI
  iintro ⟨H1, H2⟩
  icases H1 with (%H | ⟨%ms, %γs, %Hst, #Hreg, H1⟩)
  · subst H; ipureintro; intro i e1 e2 _ _ h; simp at h
  icases H2 with (%H | ⟨%ms', %γs', %Hst', #Hreg', H2⟩)
  · subst H; ipureintro; intro i e1 e2 _ _ _ h; simp at h
  icases memStorReg_same st ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  unfold memLog
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  iapply memLogL_agree γs.log k1 k2 dq1 dq2 es1 es2
  iframe

theorem memStorLogI_persist (st : Storage) (k : Nat) (dq : DFrac) (es : List EntryM) :
    memStorLogI (GF := GF) st k dq es ⊢ |==> memStorLogI st k DFrac.discard es := by
  unfold memStorLogI
  iintro (%H | ⟨%ms, %γs, %Hst, #Hreg, H⟩)
  · imodintro; ileft; ipureintro; exact H
  imod memLog_persist γs k dq es $$ H with H
  imodintro
  iright; iexists ms, γs; iframe Hreg H; ipureintro; exact Hst

theorem memStorEndI_excl (st : Storage) (e e' : Nat) :
    memStorEndI (GF := GF) st e ∗ memStorEndI st e' ⊢ False := by
  unfold memStorEndI
  iintro ⟨⟨%ms, %γs, %Hst, #Hreg, H1⟩, ⟨%ms', %γs', %Hst', #Hreg', H2⟩⟩
  icases memStorReg_same st ms ms' γs γs' Hst Hst' $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iapply memEnd_excl γs e e'
  iframe

theorem memStorCompactedI_mono (st : Storage) (c c' : Nat) (h : c' ≤ c) :
    memStorCompactedI (GF := GF) st c ⊢ memStorCompactedI st c' := by
  unfold memStorCompactedI
  iintro (%H | ⟨%ms, %γs, %Hst, #Hreg, #H⟩)
  · ileft; ipureintro; omega
  iright; iexists ms, γs; iframe Hreg
  isplitr
  · ipureintro; exact Hst
  iapply memCompacted_mono γs c c' h $$ H

/-- The storage model of an application whose `Storage`s are bare `MemoryStorage`s. -/
instance memStorageModel : StorageModel GF where
  storLog := memStorLogI
  storEnd := memStorEndI
  storCompacted := memStorCompactedI
  storLog_app := memStorLogI_app
  storLog_frac := memStorLogI_frac
  storLog_valid := memStorLogI_valid
  storLog_agree := memStorLogI_agree
  storLog_persist := memStorLogI_persist
  storLog_persistent := fun st k es => by unfold memStorLogI; infer_instance
  storLog_nil := fun st k dq => by unfold memStorLogI; iintro; ileft; ipureintro; rfl
  storEnd_excl := memStorEndI_excl
  storCompacted_persistent := fun st c => by unfold memStorCompactedI; infer_instance
  storCompacted_zero := fun st => by unfold memStorCompactedI; iintro; ileft; ipureintro; rfl
  storCompacted_mono := memStorCompactedI_mono

/-! ### The conversions, under the registry's record -/

theorem memStorLog_to (ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ storLog (memStorIface ms) k dq es -∗ memLog γs k dq es := by
  iintro #Hreg H
  ihave H : memStorLogI (memStorIface ms) k dq es $$ [H]
  · iexact H
  unfold memStorLogI
  icases H with (%H | ⟨%ms', %γs', %Hst, #Hreg', H⟩)
  · subst H; iapply memLog_nil
  icases memStorReg_same (memStorIface ms) ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem memStorLog_of (ms : Loc) (γs : MemStorNames) (k : Nat) (dq : DFrac) (es : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ memLog γs k dq es -∗ storLog (memStorIface ms) k dq es := by
  iintro #Hreg H
  ihave H : memStorLogI (GF := GF) (memStorIface ms) k dq es $$ [H]
  · unfold memStorLogI; iright; iexists ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

theorem memStorEnd_to (ms : Loc) (γs : MemStorNames) (e : Nat) :
    ⊢ memStorReg (GF := GF) ms γs -∗ storEnd (memStorIface ms) e -∗ memEnd γs e := by
  iintro #Hreg H
  ihave H : memStorEndI (memStorIface ms) e $$ [H]
  · iexact H
  unfold memStorEndI
  icases H with ⟨%ms', %γs', %Hst, #Hreg', H⟩
  icases memStorReg_same (memStorIface ms) ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem memStorEnd_of (ms : Loc) (γs : MemStorNames) (e : Nat) :
    ⊢ memStorReg (GF := GF) ms γs -∗ memEnd γs e -∗ storEnd (memStorIface ms) e := by
  iintro #Hreg H
  ihave H : memStorEndI (GF := GF) (memStorIface ms) e $$ [H]
  · unfold memStorEndI; iexists ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

theorem memStorCompacted_to (ms : Loc) (γs : MemStorNames) (c : Nat) :
    ⊢ memStorReg (GF := GF) ms γs -∗ storCompacted (memStorIface ms) c -∗ memCompacted γs c := by
  iintro #Hreg H
  ihave H : memStorCompactedI (memStorIface ms) c $$ [H]
  · iexact H
  unfold memStorCompactedI
  icases H with (%H | ⟨%ms', %γs', %Hst, #Hreg', #H⟩)
  · subst H; iapply memCompacted_zero
  icases memStorReg_same (memStorIface ms) ms ms' γs γs' rfl Hst $$ Hreg Hreg' with %Hsame
  obtain ⟨rfl, rfl⟩ := Hsame
  iexact H

theorem memStorCompacted_of (ms : Loc) (γs : MemStorNames) (c : Nat) :
    ⊢ memStorReg (GF := GF) ms γs -∗ memCompacted γs c -∗ storCompacted (memStorIface ms) c := by
  iintro #Hreg #H
  ihave H : memStorCompactedI (GF := GF) (memStorIface ms) c $$ []
  · unfold memStorCompactedI; iright; iexists ms, γs; iframe Hreg H; ipureintro; rfl
  iexact H

/-! ### The contract -/

/-- **The contract law** (generic: step 4 instantiates `J`): a registered storage with its invariant
meets `isStorageP`, at the snapshot validity `J.SV`, the compaction justification `memBnd J` and the
delivered bound `J.DL`. -/
theorem memStorage_isStorageP
    (wp_LastIndex : MemoryStorage.LastIndex.spec (GF := GF) (hG := hG))
    (wp_FirstIndex : MemoryStorage.FirstIndex.spec (GF := GF) (hG := hG))
    (wp_Term : MemoryStorage.Term.spec (GF := GF) (hG := hG))
    (wp_Entries : MemoryStorage.Entries.spec (GF := GF) (hG := hG))
    (wp_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (ms : Loc) (γs : MemStorNames) (J : MemJust GF) :
    ⊢ memStorInvP ms γs J -∗ memStorReg ms γs -∗
      isStorageP J.SV (memBnd J) J.DL (memStorIface ms) := by
  iintro #Hinv #Hreg
  ihave #Hl : memStorLock ms γs $$ []
  · iunfold memStorInvP at Hinv; icases Hinv with ⟨#Hl, -⟩; iexact Hl
  ihave #Hinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iunfold memStorLock at Hl; icases Hl with ⟨#H, -⟩; iexact H
  unfold isStorageP
  iexists (interface.mk (go.GoType.PointerType MemoryStorage.ty) #ms)
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro %e
    imodintro
    iintro %Φ He HΦ
    ihave He := memStorEnd_to ms γs e $$ Hreg He
    wp_apply wp_LastIndex ms γs e $$ [$Hl $He] as %li ⟨He, %Hli⟩
    iapply HΦ
    ihave He := memStorEnd_of ms γs e $$ Hreg He
    iframe He
    ipureintro; exact Hli
  isplitr
  · iintro %k %dq %es %i0 %ec
    imodintro
    iintro %Φ ⟨H, %Hr, #Hec⟩ HΦ
    ihave H := memStorLog_to ms γs k dq es $$ Hreg H
    wp_apply wp_Term ms γs k dq es i0 ec $$ [$Hl $H $Hec] as %t %err ⟨H, Ht⟩
    · ipureintro; exact Hr
    iapply HΦ
    ihave H := memStorLog_of ms γs k dq es $$ Hreg H
    iframe H
    icases Ht with (%Ht | ⟨%Ht, #Hc⟩)
    · ileft; ipureintro; exact Ht
    · iright
      isplitr
      · ipureintro; exact Ht
      iapply memStorCompacted_of ms γs _ $$ Hreg Hc
  isplitr
  · iintro %k %dq1 %dq2 %a %b %lo %hi %maxSize %ec
    imodintro
    iintro %Φ ⟨Ha, Hb, %Hr, #Hec⟩ HΦ
    ihave Ha := memStorLog_to ms γs k dq1 a $$ Hreg Ha
    ihave Hb := memStorLog_to ms γs (k + a.length) dq2 b $$ Hreg Hb
    wp_apply wp_Entries ms γs k dq1 dq2 a b lo hi maxSize ec $$ [$Hl $Ha $Hb $Hec]
      as %sl %es %err ⟨Ha, Hb, Hres⟩
    · ipureintro; exact Hr
    iapply HΦ $$ %sl %es %err
    ihave Ha := memStorLog_of ms γs k dq1 a $$ Hreg Ha
    ihave Hb := memStorLog_of ms γs (k + a.length) dq2 b $$ Hreg Hb
    iframe Ha Hb
    icases Hres with (⟨%He, #Hc⟩ | Hres)
    · ileft
      isplitr
      · ipureintro; exact He
      iapply memStorCompacted_of ms γs _ $$ Hreg Hc
    · iright; iexact Hres
  isplitr
  · iintro %c
    imodintro
    iintro %Φ #Hc HΦ
    ihave #Hc := memStorCompacted_to ms γs c $$ Hreg Hc
    wp_apply wp_FirstIndex ms γs c $$ [$Hl $Hc] as %fi ⟨%Hfi, #Hc'⟩
    iapply HΦ
    isplitr
    · ipureintro; exact Hfi
    iapply memStorCompacted_of ms γs _ $$ Hreg Hc'
  isplitr
  · iintro %c %esu
    imodintro
    iintro %Φ ⟨#Hc, #Hesu⟩ HΦ
    ihave #Hc := memStorCompacted_to ms γs c $$ Hreg Hc
    wp_apply wp_Snapshot ms γs J c false esu $$ [$Hinv $Hc $Hesu] as %snap %err ⟨-, Hres⟩
    · iempintro
    iapply HΦ
    icases Hres with ⟨%H, %sv, Hs, %Hsv, Hv⟩
    ihave Hs := ownSnapW_E $$ Hs
    ihave Hs := ownSnapE_weaken $$ Hs
    iright
    iframe
    ipureintro; exact ⟨H, Hsv.1⟩
  isplitr
  · iintro !> %c #Hc
    ihave #Hc := memStorCompacted_to ms γs c $$ Hreg Hc
    iapply memCompacted_bound ms γs J c $$ Hinv Hc
  iintro !> %k %dq %es H
  ihave H := memStorLog_to ms γs k dq es $$ Hreg H
  iunfold memLog at H
  icases H with ⟨H, %Hb⟩
  isplitr
  · ipureintro; exact Hb
  iapply memStorLog_of ms γs k dq es $$ Hreg
  iunfold memLog
  iframe H
  ipureintro; exact Hb

end model

end EtcdGrove
end Perennial
