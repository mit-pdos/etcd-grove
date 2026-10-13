/-
`pkg/wait`'s `*list` (`wait.go`): its own invariant, the shared vocabulary of the specs of
`list.Register`, `list.Trigger`, `list.IsRegistered` and the proof of `New`. Lean-first (no Rocq
counterpart); the contract `New` establishes from them is `isWait` (`wait/Defs.lean`).

**The shards.** A `list` holds a slice `e` of 64 `listElement`s (written once, by `New`), each a
`sync.RWMutex` `l` over a map `m` (`id ↦ chan any`; the field itself written once, by `New`, so
read-only outside the lock). The `k`-th shard has two ghost maps, named in the wait's ghost map
`γw` (`k ↪[γw]□ (γs, γr)`, persistent: what pins a reader's and a writer's view of the shard to
the same names). A shard's lock invariant (fractional, as Perennial's `RWMutex` needs) is a
`q`-fraction of the map and `q/2` of the ghost map authority `γs` mirroring it (`waitShardP`); the
other half of the authority, with the resources of each live id, is the shard's invariant
(`waitShardInv`): the id's element of `γs`, its channel's handoff (`isHandoff γh ch (waitVal γh Ψ)
True True`) with the producer's token, the registration condition `□ R id Ψ`, and its element of
`γr`. A writer (`Register`, `Trigger`), holding the lock (the whole authority half), opens the
invariant for a ghost step that moves the resources in or out.

**The registrations** (`γr`, the request path's unit 4d): every id ever registered in the shard,
to its channel's consumer token's name and its registration's flag's `g`; the invariant holds,
for each, the id's slot (`idSlot γi id`, kept forever: so a caller of `Register(id)` holding the
slot finds `id` nowhere, and the `log.Panicf("dup id")` branch is unreachable) and its flag by the
live map (`waitRegStateO`): exclusive while the id is live, discarded once a `Trigger` took it out
(`waitShard_take`). So a reader who sees `id` absent from the live map and knows it registered
gets the discarded flag (`waitShard_gone`): the registration is gone (`waitGone`).

**The reader** (`waitListReader`): one reader slot (`sync.ownRWMutex`) of each shard's lock, with
the shard's names and invariant, for `IsRegistered`.
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

/-- **A registered id's resources**, in its shard's invariant (live map's part): the channel
`ch`'s handoff (for the expectation `Ψ` the registration condition allows), its producer's token
(nothing sent yet), and `id`'s element of the shard's record `γr` (the channel's consumer token's
name and the registration's flag's). -/
def waitEntry (γr : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF) (id : w64)
    (ch : Loc) : IProp GF :=
  iprop(∃ (γh : HandoffNames) (Ψ : GoInterface → IProp GF) (g : GName),
    isHandoff (V := GoInterface) γh ch (waitVal γh Ψ) iprop(True) iprop(False) ∗
    handoffProducer γh false ∗ □ R id Ψ ∗ id ↪[γr]□ (γh.takenName, g))

/-- A registration's flag `g` by whether its id is in the live map (`o`, its lookup): exclusive
while live, discarded once gone. -/
def waitRegStateO (o : Option Loc) (g : GName) : IProp GF :=
  match o with
  | some _ => dghostVar g (DFrac.own 1) ()
  | none => dghostVar g DFrac.discard ()

theorem waitRegStateO_some (c : Loc) (g : GName) :
    waitRegStateO (GF := GF) (some c) g = dghostVar g (DFrac.own 1) () := rfl

theorem waitRegStateO_none (g : GName) :
    waitRegStateO (GF := GF) none g = dghostVar g DFrac.discard () := rfl

/-- The registrations' part of a shard's invariant (`G`: every id ever registered in the shard,
to its consumer token's and flag's names): each id's slot, and its flag by the live map `M`. -/
def waitRegs (γi : IdNames) (M : GMap w64 Loc) (G : GMap w64 (GName × GName)) : IProp GF :=
  iprop([∗map] id ↦ tg ∈ G, idSlot γi id ∗ waitRegStateO (M !! id) tg.2)

/-- **A shard's invariant** (ghost maps `γs`, the live registrations mirroring the Go map, and
`γr`, every registration ever made in the shard): the other half of `γs`'s authority, each live
id's element and resources, `γr`'s authority and each registration's slot and flag. -/
def waitShardInv (γi : IdNames) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (γs γr : GName) : IProp GF :=
  iprop(∃ (M : GMap w64 Loc) (G : GMap w64 (GName × GName)), ghostMapAuth γs (1 : Qp).half M ∗
    ([∗map] id ↦ ch ∈ M, id ↪[γs] ch ∗ waitEntry γr R id ch) ∗
    ghostMapAuth γr 1 G ∗ waitRegs γi M G)

/-- **Shard `ea`, the `k`-th** (persistent): its names in the wait's ghost map `γw`, its map
field, its lock's writer guard, its invariant. -/
def waitShard (γi : IdNames) (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (ea : Loc) (k : w64) : IProp GF :=
  iprop(∃ (mref : Loc) (γs γr : GName), k ↪[γw]□ (γs, γr) ∗ waitShardMap ea ↦□ mref ∗
    sync.isRWMutexGuard (waitShardLock ea) (waitShardP mref γs) ∗
    inv waitShardN (waitShardInv γi R γs γr))

instance waitShard_persistent (γi : IdNames) (γw : GName)
    (R : w64 → (GoInterface → IProp GF) → IProp GF) (ea : Loc) (k : w64) :
    Persistent (waitShard (GF := GF) γi γw R ea k) := by
  unfold waitShard; infer_instance

/-- **The `*list` `l`** (persistent): its 64 shards. -/
def waitList (l : Loc) (γi : IdNames) (γw : GName)
    (R : w64 → (GoInterface → IProp GF) → IProp GF) : IProp GF :=
  iprop(∃ sl : GoSlice, structFieldRef wait.list' go!"e" l ↦□ sl ∗ ⌜sint.Z sl.len = 64⌝ ∗
    □ (∀ i : Nat, ⌜i < 64⌝ -∗ waitShard γi γw R (waitShardAddr sl i) (W64 i)))

instance waitList_persistent (l : Loc) (γi : IdNames) (γw : GName)
    (R : w64 → (GoInterface → IProp GF) → IProp GF) : Persistent (waitList (GF := GF) l γi γw R) := by
  unfold waitList; infer_instance

/-- A reader slot of shard `ea`'s lock, the `k`-th, with the shard's names and invariant. -/
def waitShardReader (γi : IdNames) (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (ea : Loc) (k : w64) : IProp GF :=
  iprop(∃ (mref : Loc) (γs γr : GName), k ↪[γw]□ (γs, γr) ∗ waitShardMap ea ↦□ mref ∗
    sync.ownRWMutex (waitShardLock ea) (waitShardP mref γs) ∗
    inv waitShardN (waitShardInv γi R γs γr))

/-- **The reader's resource** of the `*list` `l`: a reader slot of each shard's lock. -/
def waitListReader (l : Loc) (γi : IdNames) (γw : GName)
    (R : w64 → (GoInterface → IProp GF) → IProp GF) : IProp GF :=
  iprop(∃ sl : GoSlice, structFieldRef wait.list' go!"e" l ↦□ sl ∗ ⌜sint.Z sl.len = 64⌝ ∗
    [∗list] i ↦ _u ∈ List.replicate 64 (), waitShardReader γi γw R (waitShardAddr sl i) (W64 i))

/-! ## Ghost steps -/

theorem waitAuth_halves (γs : GName) (M : GMap w64 Loc) :
    ghostMapAuth (GF := GF) γs 1 M ⊣⊢
      ghostMapAuth γs (1 : Qp).half M ∗ ghostMapAuth γs (1 : Qp).half M := by
  have h := (ghostMapAuth_fractional (GF := GF) (K := w64) (V := Loc) γs M).fractional
    (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

/-- The registrations' flags depend only on the live map's lookups at their ids. -/
theorem waitRegs_congr (γi : IdNames) (M M' : GMap w64 Loc) (G : GMap w64 (GName × GName))
    (h : ∀ k v, G !! k = some v → M' !! k = M !! k) :
    ([∗map] id ↦ tg ∈ G, idSlot (GF := GF) γi id ∗ waitRegStateO (M !! id) tg.2) ⊢
      [∗map] id ↦ tg ∈ G, idSlot γi id ∗ waitRegStateO (M' !! id) tg.2 := by
  refine BigSepM.bigSepM_mono (fun {k v} hk => ?_)
  rw [h k v (by simpa [gmap_get?_eq] using hk)]

/-- Two slots of the same id: impossible. -/
theorem waitSlot_absurd (γi : IdNames) (id : w64) :
    ⊢ idSlot (GF := GF) γi id -∗ idSlot γi id -∗ False := by
  iintro Hs Hs'
  iunfold idSlot at Hs Hs'
  ihave %Hv := ghostMapElem_valid_2 _ _ _ _ _ _ $$ Hs Hs'
  exfalso
  exact absurd (DFrac.valid_op_own Hv.1) (by simp)

/-- Taking `id`'s entry (if any) out of its shard, the writer holding the lock's half: its
registration's flag is discarded (gone). -/
theorem waitShard_take (γi : IdNames) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (γs γr : GName) (id : w64) (M : GMap w64 Loc) :
    ⊢ inv waitShardN (waitShardInv γi R γs γr) -∗ £ 1 -∗ ghostMapAuth γs (1 : Qp).half M ={⊤}=∗
      ghostMapAuth γs (1 : Qp).half (GMap.delete id M) ∗
      (match M !! id with | some ch => waitEntry γr R id ch | none => iprop(True)) := by
  iintro #Hinv Hlc Hg
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑waitShardN) $$ Hlc Hi with Hi
  iunfold waitShardInv at Hi
  icases Hi with ⟨%M', %G, Hg', Hm, Hgr, Hregs⟩
  ihave %Heq := ghostMapAuth_agree γs _ _ M M' $$ Hg Hg'
  subst Heq
  cases h : M !! id with
  | none =>
    have hd : GMap.delete id M = M := by
      ext k; by_cases e : id = k
      · subst e; simp [GMap.lookup_delete_iff, h]
      · simp [GMap.lookup_delete_iff, e]
    rw [hd]
    imod Hclose $$ [Hg' Hm Hgr Hregs] with -
    · inext; iunfold waitShardInv; iexists M, G; iframe
    imodintro; iframe
  | some ch =>
    icases (BigSepM.bigSepM_delete (PROP := IProp GF)
      (Φ := fun id ch => iprop(id ↪[γs] ch ∗ waitEntry γr R id ch)) (m := M) h).1 $$ Hm
      with ⟨⟨Hel, Hent⟩, Hm⟩
    iunfold waitEntry at Hent
    icases Hent with ⟨%γh, %Ψ, %g, #Hh, Hp, #HR, #Hr⟩
    ihave %HG := ghost_map_lookup $$ Hgr Hr
    iunfold waitRegs at Hregs
    icases (BigSepM.bigSepM_delete (PROP := IProp GF)
      (Φ := fun id (tg : GName × GName) => iprop(idSlot (GF := GF) γi id ∗
        waitRegStateO (GF := GF) (M !! id) tg.2)) (m := G) HG).1 $$ Hregs
      with ⟨⟨Hs, Hst⟩, Hregs⟩
    rw [h, waitRegStateO_some]
    imod dghostVar_persist $$ Hst with #Hst
    ihave Hga := (waitAuth_halves γs M).2 $$ [Hg Hg']
    · iframe
    imod ghost_map_delete $$ Hga Hel with Hga
    icases (waitAuth_halves γs _).1 $$ Hga with ⟨Hg, Hg'⟩
    imod Hclose $$ [Hg' Hm Hgr Hregs Hs] with -
    · inext; iunfold waitShardInv; iexists _, G; iframe Hg' Hgr; iframe Hm
      iunfold waitRegs
      iapply (BigSepM.bigSepM_delete (PROP := IProp GF)
        (Φ := fun k (tg : GName × GName) => iprop(idSlot (GF := GF) γi k ∗
          waitRegStateO (GF := GF) ((GMap.delete id M) !! k) tg.2)) (m := G) HG).2
      isplitl [Hs]
      · iframe Hs
        rw [GMap.lookup_delete, waitRegStateO_none]
        iexact Hst
      iapply (waitRegs_congr γi M (GMap.delete id M) (GMap.delete id G) (fun k v hk => by
        have hne : id ≠ k := by
          intro e; subst e; simp at hk
        exact GMap.lookup_delete_ne M hne))
      iexact Hregs
    imodintro
    iframe Hg
    iunfold waitEntry
    iexists γh, Ψ, g
    iframe Hp
    iframe #

/-- An id live in its shard holds its slot in the registrations: a second slot is impossible
(`Register`'s `log.Panicf("dup id")`). -/
theorem waitShard_dup (γi : IdNames) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (γs γr : GName) (id : w64) (M : GMap w64 Loc) (ch : Loc) (h : M !! id = some ch) :
    ⊢ inv waitShardN (waitShardInv γi R γs γr) -∗ £ 1 -∗ ghostMapAuth γs (1 : Qp).half M -∗
      idSlot γi id ={⊤}=∗ False := by
  iintro #Hinv Hlc Hg Hs
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑waitShardN) $$ Hlc Hi with Hi
  iunfold waitShardInv at Hi
  icases Hi with ⟨%M', %G, Hg', Hm, Hgr, Hregs⟩
  ihave %Heq := ghostMapAuth_agree γs _ _ M M' $$ Hg Hg'
  subst Heq
  icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
    (Φ := fun id ch => iprop(id ↪[γs] ch ∗ waitEntry γr R id ch)) (m := M) h).1 $$ Hm
    with ⟨⟨-, Hent⟩, -⟩
  iunfold waitEntry at Hent
  icases Hent with ⟨%γh, %Ψ, %g, -, -, -, #Hr⟩
  ihave %HG := ghost_map_lookup $$ Hgr Hr
  iunfold waitRegs at Hregs
  icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
    (Φ := fun id (tg : GName × GName) => iprop(idSlot (GF := GF) γi id ∗
      waitRegStateO (GF := GF) (M !! id) tg.2)) (m := G) HG).1 $$ Hregs with ⟨⟨Hs', -⟩, -⟩
  iexfalso
  iapply waitSlot_absurd γi id $$ Hs Hs'

/-- **Registering** `id` (not live in its shard; its slot) with the channel `ch`'s handoff: the
id's live entry and its registration record, with a fresh flag (live). -/
theorem waitShard_register (γi : IdNames) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (γs γr : GName) (id : w64) (M : GMap w64 Loc) (ch : Loc) (h : M !! id = none)
    (γh : HandoffNames) (Ψ : GoInterface → IProp GF) :
    ⊢ inv waitShardN (waitShardInv γi R γs γr) -∗ £ 1 -∗ ghostMapAuth γs (1 : Qp).half M -∗
      idSlot γi id -∗
      isHandoff (V := GoInterface) γh ch (waitVal γh Ψ) iprop(True) iprop(False) -∗
      handoffProducer γh false -∗ □ R id Ψ ={⊤}=∗
      ghostMapAuth γs (1 : Qp).half (<[id := ch]> M) ∗ ∃ g : GName, id ↪[γr]□ (γh.takenName, g) := by
  iintro #Hinv Hlc Hg Hs #Hh Hp #HR
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑waitShardN) $$ Hlc Hi with Hi
  iunfold waitShardInv at Hi
  icases Hi with ⟨%M', %G, Hg', Hm, Hgr, Hregs⟩
  ihave %Heq := ghostMapAuth_agree γs _ _ M M' $$ Hg Hg'
  subst Heq
  iunfold waitRegs at Hregs
  cases hG : G !! id with
  | some tg =>
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
      (Φ := fun id (tg : GName × GName) => iprop(idSlot (GF := GF) γi id ∗
        waitRegStateO (GF := GF) (M !! id) tg.2)) (m := G) hG).1 $$ Hregs with ⟨⟨Hs', -⟩, -⟩
    iexfalso
    iapply waitSlot_absurd γi id $$ Hs Hs'
  | none =>
    imod dghostVar_alloc (GF := GF) () with ⟨%g, Hflag⟩
    imod ghost_map_insert_persist id (γh.takenName, g) hG $$ Hgr with ⟨Hgr, #Hr⟩
    ihave Hga := (waitAuth_halves γs M).2 $$ [Hg Hg']
    · iframe
    imod ghost_map_insert id ch h $$ Hga with ⟨Hga, Hel⟩
    icases (waitAuth_halves γs _).1 $$ Hga with ⟨Hg, Hg'⟩
    imod Hclose $$ [Hg' Hm Hgr Hregs Hel Hp Hs Hflag] with -
    · inext; iunfold waitShardInv; iexists _, _; iframe Hg' Hgr
      isplitl [Hm Hel Hp]
      · iapply (BigSepM.bigSepM_insert (PROP := IProp GF)
          (Φ := fun id ch => iprop(id ↪[γs] ch ∗ waitEntry γr R id ch)) (m := M) (x := ch) h).2
        iframe Hm Hel
        iunfold waitEntry
        iexists γh, Ψ, g
        iframe Hp
        iframe #
      iunfold waitRegs
      iapply (BigSepM.bigSepM_insert (PROP := IProp GF)
        (Φ := fun k (tg : GName × GName) => iprop(idSlot (GF := GF) γi k ∗
          waitRegStateO (GF := GF) ((<[id := ch]> M) !! k) tg.2)) (m := G)
        (x := (γh.takenName, g)) hG).2
      isplitl [Hs Hflag]
      · iframe Hs
        rw [GMap.lookup_insert, waitRegStateO_some]
        iexact Hflag
      iapply (waitRegs_congr γi M (<[id := ch]> M) G (fun k v hk => by
        have hne : id ≠ k := by
          intro e; subst e; rw [hG] at hk; cases hk
        exact GMap.lookup_insert_ne M ch hne))
      iexact Hregs
    imodintro
    iframe Hg
    iexists g
    iexact Hr

/-- **A registration not live is gone**: `id` (registered in the shard, `γr`'s element) not in
the live map `M` (as a reader sees it, any fraction of `γs`'s authority) has its flag discarded. -/
theorem waitShard_gone (γi : IdNames) (R : w64 → (GoInterface → IProp GF) → IProp GF)
    (γs γr : GName) (id : w64) (M : GMap w64 Loc) (q : Qp) (t g : GName) (h : M !! id = none) :
    ⊢ inv waitShardN (waitShardInv γi R γs γr) -∗ £ 1 -∗ ghostMapAuth γs q M -∗
      id ↪[γr]□ (t, g) ={⊤}=∗ ghostMapAuth γs q M ∗ dghostVar g DFrac.discard () := by
  iintro #Hinv Hlc Hg #Hr
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑waitShardN) $$ Hlc Hi with Hi
  iunfold waitShardInv at Hi
  icases Hi with ⟨%M', %G, Hg', Hm, Hgr, Hregs⟩
  ihave %Heq := ghostMapAuth_agree γs _ _ M M' $$ Hg Hg'
  subst Heq
  ihave %HG := ghost_map_lookup $$ Hgr Hr
  iunfold waitRegs at Hregs
  icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
    (Φ := fun id (tg : GName × GName) => iprop(idSlot (GF := GF) γi id ∗
      waitRegStateO (GF := GF) (M !! id) tg.2)) (m := G) HG).1 $$ Hregs with ⟨⟨Hs, Hst⟩, Hregs⟩
  rw [h, waitRegStateO_none]
  icases Hst with #Hst
  imod Hclose $$ [Hg' Hm Hgr Hregs Hs] with -
  · inext; iunfold waitShardInv; iexists M, G; iframe Hg' Hm Hgr
    iunfold waitRegs
    iapply Hregs
    iframe Hs
    iexact Hst
  imodintro
  iframe Hg Hst

end defs

end EtcdGrove
end Perennial
