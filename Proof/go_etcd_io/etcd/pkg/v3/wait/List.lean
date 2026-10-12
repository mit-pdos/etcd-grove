/-
`pkg/wait`'s `*list` (`wait.go`): its own invariant, the shared vocabulary of the specs of
`list.Register`, `list.Trigger`, `list.IsRegistered` and the proof of `New`. Lean-first (no Rocq
counterpart); the contract `New` establishes from them is `isWait` (`wait/Defs.lean`).

**The shards.** A `list` holds a slice `e` of 64 `listElement`s (written once, by `New`), each a
`sync.RWMutex` `l` over a map `m` (`id ↦ chan any`; the field itself written once, by `New`, so
read-only outside the lock). A shard's lock invariant (fractional, as Perennial's `RWMutex` needs)
is a `q`-fraction of the map and `q/2` of a ghost map authority `γs` mirroring it
(`waitShardP`); the other half of the authority, with the resources of each registered id, is the
shard's invariant (`waitShardInv`): the id's element of `γs`, its channel's handoff
(`isHandoff γh ch (waitVal γh Ψ) True True`) with the producer's token, the registration
condition `□ R id Ψ`, and the record `waitRegd γw id γh.takenName`. A writer (`Register`,
`Trigger`), holding the lock (the whole authority half), opens the invariant for a ghost step that
moves the resources in or out.

**The registered ids** (`waitRegInv`): the ghost map `γw` of every id ever registered (to its
channel's consumer token's name), each with the id's slot (`idSlot γi id`), kept forever. So a
caller of `Register(id)` holding the slot finds `id` in no shard (a shard's entry records it in
`γw`, whose invariant holds the slot): the `log.Panicf("dup id")` branch is unreachable.

**The reader** (`waitListReader`): one reader slot (`sync.ownRWMutex`) of each shard's lock, for
`IsRegistered`.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.wait.Defs
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.wait

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

def waitShardN : Namespace := nroot .@ "wait_shard"
def waitRegN : Namespace := nroot .@ "wait_reg"

theorem wait_qp_half_add (q1 q2 : Qp) : (q1 + q2).half = q1.half + q2.half := by
  apply Subtype.ext
  show (q1.val + q2.val) / 2 = q1.val / 2 + q2.val / 2
  grind

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of shard `i` (`&w.e[i]`) of the slice `sl`. -/
abbrev waitShardAddr (sl : GoSlice) (i : Nat) : Loc :=
  sliceIndexRef wait.listElement (i : Int) sl

/-- The address of a shard's lock. -/
abbrev waitShardLock (ea : Loc) : Loc := structFieldRef wait.listElement go!"l" ea

/-- The address of a shard's map field. -/
abbrev waitShardMap (ea : Loc) : Loc := structFieldRef wait.listElement go!"m" ea

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A shard's lock invariant** `P q`: a `q`-fraction of its map `mref`'s contents `M`, and
`q/2` of the ghost map `γs` mirroring them. -/
def waitShardP (mref : Loc) (γs : GName) (q : Qp) : IProp GF :=
  iprop(∃ M : GMap w64 Loc, ownMap mref (DFrac.own q) M ∗ ghostMapAuth γs q.half M)

theorem wait_ownMap_fractional (mref : Loc) (m : GMap w64 Loc) :
    Fractional (fun q : Qp => (ownMap (GF := GF) mref (DFrac.own q) m : IProp GF)) where
  fractional p q := by
    rw [ownMap_unseal]
    have hh := fun mv => (heapPointsto_fractional mref mv).fractional p q
    constructor
    · iintro H
      unfold ownMapDef
      iNamed H
      icases (hh mv).1 $$ Hown with ⟨H1, H2⟩
      isplitl [H1]
      · iexists mv, mp; simp only [named]; iframe H1; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
      · iexists mv, mp; simp only [named]; iframe H2; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
    · iintro ⟨H1, H2⟩
      unfold ownMapDef
      iNamedSuffix H1 "1"
      iNamedSuffix H2 "2"
      icombine Hown1 Hown2 gives % ⟨_, Hmv⟩
      subst Hmv
      iexists mv, mp
      simp only [named]
      isplitl [Hown1 Hown2]
      · iapply (hh mv).2; iframe
      ipureintro; exact ⟨His_map2, Hagree2, Hdom2, Hdefault2⟩

instance waitShardP_fractional (mref : Loc) (γs : GName) :
    Fractional (waitShardP (GF := GF) mref γs) where
  fractional q1 q2 := by
    have hm := fun M => (wait_ownMap_fractional (GF := GF) mref M).fractional q1 q2
    have hg := fun M => (ghostMapAuth_fractional (GF := GF) (K := w64) (V := Loc) γs M).fractional
      q1.half q2.half
    unfold waitShardP
    refine ⟨?_, ?_⟩
    · iintro ⟨%M, Hm, Hg⟩
      rw [wait_qp_half_add]
      icases (hm M).1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (hg M).1 $$ Hg with ⟨Hg1, Hg2⟩
      isplitl [Hm1 Hg1]
      · iexists M; iframe
      · iexists M; iframe
    · iintro ⟨⟨%M1, Hm1, Hg1⟩, ⟨%M2, Hm2, Hg2⟩⟩
      ihave %Heq := ghostMapAuth_agree γs _ _ M1 M2 $$ Hg1 Hg2
      subst Heq
      iexists M1
      rw [wait_qp_half_add]
      isplitl [Hm1 Hm2]
      · iapply (hm M1).2; iframe
      · iapply (hg M1).2; iframe

/-- **A registered id's resources**, in its shard's invariant: the channel `ch`'s handoff (for the
expectation `Ψ` the registration condition allows), its producer's token (nothing sent yet), and
the record of the registration with the channel's consumer token's name. -/
def waitEntry (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF) (id : w64)
    (ch : Loc) : IProp GF :=
  iprop(∃ (γh : HandoffNames) (Ψ : GoInterface → IProp GF),
    isHandoff (V := GoInterface) γh ch (waitVal γh Ψ) iprop(True) iprop(False) ∗
    handoffProducer γh false ∗ □ R id Ψ ∗ waitRegd γw id γh.takenName)

/-- **A shard's invariant** (ghost map `γs`): the other half of the authority, and each
registered id's element and resources. -/
def waitShardInv (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF) (γs : GName) :
    IProp GF :=
  iprop(∃ M : GMap w64 Loc, ghostMapAuth γs (1 : Qp).half M ∗
    [∗map] id ↦ ch ∈ M, id ↪[γs] ch ∗ waitEntry γw R id ch)

/-- **The registered ids' invariant**: every id ever registered (`γw`), with its slot. -/
def waitRegInv (γi : IdNames) (γw : GName) : IProp GF :=
  iprop(∃ G : GMap w64 GName, ghostMapAuth γw 1 G ∗ [∗map] id ↦ _t ∈ G, idSlot γi id)

instance waitRegInv_timeless (γi : IdNames) (γw : GName) :
    Timeless (waitRegInv (GF := GF) γi γw) := by
  unfold waitRegInv idSlot; infer_instance

/-- **Shard `ea`** (persistent): its map field, its lock's writer guard, its invariant. -/
def waitShard (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF) (ea : Loc) :
    IProp GF :=
  iprop(∃ (mref : Loc) (γs : GName), waitShardMap ea ↦□ mref ∗
    sync.isRWMutexGuard (waitShardLock ea) (waitShardP mref γs) ∗
    inv waitShardN (waitShardInv γw R γs))

instance waitShard_persistent (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (ea : Loc) : Persistent (waitShard (GF := GF) γw R ea) := by
  unfold waitShard; infer_instance

/-- **The `*list` `l`** (persistent): its 64 shards and the registered ids' invariant. -/
def waitList (l : Loc) (γi : IdNames) (γw : GName)
    (R : w64 → (GoInterface → IProp GF) → IProp GF) : IProp GF :=
  iprop(∃ sl : GoSlice, structFieldRef wait.list' go!"e" l ↦□ sl ∗ ⌜sint.Z sl.len = 64⌝ ∗
    inv waitRegN (waitRegInv γi γw) ∗
    □ (∀ i : Nat, ⌜i < 64⌝ -∗ waitShard γw R (waitShardAddr sl i)))

instance waitList_persistent (l : Loc) (γi : IdNames) (γw : GName)
    (R : w64 → (GoInterface → IProp GF) → IProp GF) : Persistent (waitList (GF := GF) l γi γw R) := by
  unfold waitList; infer_instance

/-- A reader slot of shard `ea`'s lock. -/
def waitShardReader (ea : Loc) : IProp GF :=
  iprop(∃ (mref : Loc) (γs : GName), waitShardMap ea ↦□ mref ∗
    sync.ownRWMutex (waitShardLock ea) (waitShardP mref γs))

/-- **The reader's resource** of the `*list` `l`: a reader slot of each shard's lock. -/
def waitListReader (l : Loc) : IProp GF :=
  iprop(∃ sl : GoSlice, structFieldRef wait.list' go!"e" l ↦□ sl ∗ ⌜sint.Z sl.len = 64⌝ ∗
    [∗list] i ↦ _u ∈ List.replicate 64 (), waitShardReader (waitShardAddr sl i))

/-! ## Ghost steps -/

theorem waitAuth_halves (γs : GName) (M : GMap w64 Loc) :
    ghostMapAuth (GF := GF) γs 1 M ⊣⊢
      ghostMapAuth γs (1 : Qp).half M ∗ ghostMapAuth γs (1 : Qp).half M := by
  have h := (ghostMapAuth_fractional (GF := GF) (K := w64) (V := Loc) γs M).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

/-- Taking `id`'s entry (if any) out of its shard, the writer holding the lock's half. -/
theorem waitShard_take (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (γs : GName) (id : w64) (M : GMap w64 Loc) :
    ⊢ inv waitShardN (waitShardInv γw R γs) -∗ £ 1 -∗ ghostMapAuth γs (1 : Qp).half M ={⊤}=∗
      ghostMapAuth γs (1 : Qp).half (GMap.delete id M) ∗
      (match M !! id with | some ch => waitEntry γw R id ch | none => iprop(True)) := by
  iintro #Hinv Hlc Hg
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑waitShardN) $$ Hlc Hi with Hi
  iunfold waitShardInv at Hi
  icases Hi with ⟨%M', Hg', Hm⟩
  ihave %Heq := ghostMapAuth_agree γs _ _ M M' $$ Hg Hg'
  subst Heq
  cases h : M !! id with
  | none =>
    have hd : GMap.delete id M = M := by
      ext k; by_cases e : id = k
      · subst e; simp [GMap.lookup_delete_iff, h]
      · simp [GMap.lookup_delete_iff, e]
    rw [hd]
    imod Hclose $$ [Hg' Hm] with -
    · inext; iunfold waitShardInv; iexists M; iframe
    imodintro; iframe
  | some ch =>
    icases (BigSepM.bigSepM_delete (PROP := IProp GF)
      (Φ := fun id ch => iprop(id ↪[γs] ch ∗ waitEntry γw R id ch)) (m := M) h).1 $$ Hm
      with ⟨⟨Hel, Hent⟩, Hm⟩
    ihave Hga := (waitAuth_halves γs M).2 $$ [Hg Hg']
    · iframe
    imod ghost_map_delete $$ Hga Hel with Hga
    icases (waitAuth_halves γs _).1 $$ Hga with ⟨Hg, Hg'⟩
    imod Hclose $$ [Hg' Hm] with -
    · inext; iunfold waitShardInv; iexists _; iframe Hg'; iexact Hm
    imodintro; iframe

/-- A registered id's record, from its shard: `M !! id = some ch`. -/
theorem waitShard_regd (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (γs : GName) (id : w64) (M : GMap w64 Loc) (ch : Loc) (h : M !! id = some ch) :
    ⊢ inv waitShardN (waitShardInv γw R γs) -∗ £ 1 -∗ ghostMapAuth γs (1 : Qp).half M ={⊤}=∗
      ghostMapAuth γs (1 : Qp).half M ∗ ∃ t, waitRegd γw id t := by
  iintro #Hinv Hlc Hg
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑waitShardN) $$ Hlc Hi with Hi
  iunfold waitShardInv at Hi
  icases Hi with ⟨%M', Hg', Hm⟩
  ihave %Heq := ghostMapAuth_agree γs _ _ M M' $$ Hg Hg'
  subst Heq
  icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
      (Φ := fun id ch => iprop(id ↪[γs] ch ∗ waitEntry γw R id ch)) (m := M) h).1 $$ Hm
    with ⟨⟨Hel, Hent⟩, Hm⟩
  iunfold waitEntry at Hent
  icases Hent with ⟨%γh, %Ψ, #Hh, Hp, #HR, #Hr⟩
  imod Hclose $$ [Hg' Hm Hel Hp] with -
  · inext; iunfold waitShardInv; iexists M; iframe Hg'
    iapply Hm
    iframe Hel
    iunfold waitEntry
    iexists γh, Ψ
    iframe Hp
    iframe #
  imodintro
  iframe Hg
  iexists γh.takenName
  iexact Hr

/-- The slot of a registered id is the invariant's: no one else holds it. -/
theorem waitReg_absurd (γi : IdNames) (γw : GName) (id : w64) (t : GName) :
    ⊢ inv waitRegN (waitRegInv (GF := GF) γi γw) -∗ waitRegd γw id t -∗ idSlot γi id ={⊤}=∗
      False := by
  iintro #Hinv #Hr Hs
  iinv Hinv with Hi Hclose
  icases Hi with >Hi
  iunfold waitRegInv at Hi
  icases Hi with ⟨%G, Hg, Hm⟩
  iunfold waitRegd at Hr
  ihave %Hl := ghost_map_lookup $$ Hg Hr
  icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
      (Φ := fun id (_ : GName) => idSlot (GF := GF) γi id) (m := G) Hl).1 $$ Hm with ⟨Hs', -⟩
  iunfold idSlot at Hs Hs'
  ihave %Hv := ghostMapElem_valid_2 _ _ _ _ _ _ $$ Hs Hs'
  exfalso
  exact absurd (DFrac.valid_op_own Hv.1) (by simp)

/-- Registering `id` (its slot) with the consumer token named `t`. -/
theorem waitReg_insert (γi : IdNames) (γw : GName) (id : w64) (t : GName) :
    ⊢ inv waitRegN (waitRegInv (GF := GF) γi γw) -∗ idSlot γi id ={⊤}=∗ waitRegd γw id t := by
  iintro #Hinv Hs
  iinv Hinv with Hi Hclose
  icases Hi with >Hi
  iunfold waitRegInv at Hi
  icases Hi with ⟨%G, Hg, Hm⟩
  cases h : G !! id with
  | some t' =>
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
        (Φ := fun id (_ : GName) => idSlot (GF := GF) γi id) (m := G) h).1 $$ Hm with ⟨Hs', -⟩
    iunfold idSlot at Hs Hs'
    ihave %Hv := ghostMapElem_valid_2 _ _ _ _ _ _ $$ Hs Hs'
    exfalso
    exact absurd (DFrac.valid_op_own Hv.1) (by simp)
  | none =>
    imod ghost_map_insert_persist id t h $$ Hg with ⟨Hg, #Hr⟩
    imod Hclose $$ [Hg Hm Hs] with -
    · inext; iunfold waitRegInv; iexists _; iframe Hg
      iapply (BigSepM.bigSepM_insert (PROP := IProp GF)
        (Φ := fun id (_ : GName) => idSlot (GF := GF) γi id) (m := G) (x := t) h).2
      iframe
    imodintro
    iunfold waitRegd
    iexact Hr

/-- Adding `id`'s entry to its shard (not registered there), the writer holding the lock's
half. -/
theorem waitShard_put (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (γs : GName) (id : w64) (M : GMap w64 Loc) (ch : Loc) (h : M !! id = none) :
    ⊢ inv waitShardN (waitShardInv γw R γs) -∗ £ 1 -∗ ghostMapAuth γs (1 : Qp).half M -∗
      waitEntry γw R id ch ={⊤}=∗ ghostMapAuth γs (1 : Qp).half (<[id := ch]> M) := by
  iintro #Hinv Hlc Hg Hent
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑waitShardN) $$ Hlc Hi with Hi
  iunfold waitShardInv at Hi
  icases Hi with ⟨%M', Hg', Hm⟩
  ihave %Heq := ghostMapAuth_agree γs _ _ M M' $$ Hg Hg'
  subst Heq
  ihave Hga := (waitAuth_halves γs M).2 $$ [Hg Hg']
  · iframe
  imod ghost_map_insert id ch h $$ Hga with ⟨Hga, Hel⟩
  icases (waitAuth_halves γs _).1 $$ Hga with ⟨Hg, Hg'⟩
  imod Hclose $$ [Hg' Hm Hel Hent] with -
  · inext; iunfold waitShardInv; iexists _; iframe Hg'
    iapply (BigSepM.bigSepM_insert (PROP := IProp GF)
      (Φ := fun id ch => iprop(id ↪[γs] ch ∗ waitEntry γw R id ch)) (m := M) (x := ch) h).2
    iframe
  imodintro
  iexact Hg

end defs

end EtcdGrove
end Perennial
