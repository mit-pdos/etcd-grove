/-
Port of `election_proof/memstorage_instance.v` (at feb5c73d4).

### `MemoryStorage` meets the `Storage` contract

`isStorageWith (ownMemoryStorage ms) st` for `st` the interface value holding
`ms : *MemoryStorage` -- the contract `InvStorage.lean` states of a client-supplied
`Storage`, against raft's own implementation of it.

This is not in `InvMemstorage.lean`, where the predicate lives, because it is built from
the five method collections, which import that file; it is a file of its own, below the
links (`Link.lean`), with no triple of its own to state (the Hoare statements are
`isStorageWith`'s, and the proofs are the collections').

Lean notes: the method clauses of `isStorageWith` call `methods i.ty go!"M" i.v`, and the
collections' specs call `ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"M"`; for
`i = interface.mk (go.GoType.PointerType MemoryStorage.ty) #ms` the two are the same term
up to unfolding, so `wp_apply` of the collection's result closes each clause directly (as
Perennial's `sync.Mutex_is_Locker` does).
### The `StorageModel` instance for `*MemoryStorage` (2026-10-16, stage R7a)

`isStorageWith` above is the contract against `ownMemoryStorage ms γs` itself; raft's node
specs take it against the class's `ownStorage st` (`isStorage st`), so an application whose
`Storage` is a bare `*MemoryStorage` (etcd's server: `raft.NewMemoryStorage()` passed as
`Config.Storage`) needs an instance of `StorageModel` whose `ownStorage (memStorIface ms) σ`
is `ownMemoryStorage ms γs σ`. The instance (`memStorageModel`) recovers a storage's ghost
names from its pointer through a **registry**, a ghost map from the pointer to the names
(`memStorReg ms γs`, persistent), given by the class `MemStorReg` (its name, allocated by the
application before the run: `ghost_map_alloc_empty`). The registry's authority is the
application's, not an invariant's: registering a storage (`memStorReg_register`) needs its
pointer absent from the map, which the application knows of the map it holds (nothing
physical of a `MemoryStorage` is left over for an invariant to keep, as the key-value store's registry
keeps half of its own struct's field; `Proof/github_com/mit_pdos/etcd_grove/examples/kv/
Defs.lean`). A wrong registration is harmless: `ownStorage` then cannot be established for
that storage (its real names disagree).

`ownStorage` carries the snapshot premise of `is_Storage_MemoryStorage`, `σ.prev.index' ≠ 0 →
σ.ss.index' ≠ 0` (the contract's `Snapshot` clause promises a non-empty snapshot once the
storage is compacted, D11; until 2026-10-16, stage R8a, it promised one outright and the
premise was `σ.ss.index' ≠ 0`): a bare `MemoryStorage` is a `Storage` from `NewMemoryStorage()`
on (`memOwnStorage_empty`), after `ApplySnapshot` at any index (`memOwnStorage_applied`), and
after a `CreateSnapshot`/`Compact` pair, which keeps `prev.index ≤ ss.index`. The conversions
(`memOwnStorage_at`/`_intro`,
`memAppendRight_at`, `memAppendReceipt_intro`) go between the class's predicates and
`ownMemoryStorage`/`memAppendTok`/`memAppendedTok` under `memStorReg ms γs`;
`memStorage_isStorage` is the contract and `memStorage_Append` the application's `Append` in
the contract's terms (`appendRight` in, `appendReceipt` out), under `MemoryStorage.Append`'s
own premise: the batch's last index at most `2^61`.
-/
module

import Proof.go_etcd_io.raft.v3.Link
public import Proof.go_etcd_io.raft.v3.MemCertLink

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

end proof

/-! ## The `StorageModel` instance for `*MemoryStorage` (2026-10-16, stage R7a) -/

set_option linter.unusedSectionVars false

/-- The registry's ghost name: a class, so that `memStorageModel` can be an instance. The
application allocates it before the run (`ghost_map_alloc_empty` at `GMap Loc MemStorNamesRec`)
and holds its authority (`memStorRegAuth`). -/
class MemStorReg (GF : BundledGFunctors) where
  memStorRegName : GName

/-- A storage's names, as the registry records them. -/
abbrev MemStorNamesRec :=
  GName × GName × GName × GName × GName × GName × GName × GName × GName × GName × Int × GName

def MemStorNames.tuple (γs : MemStorNames) : MemStorNamesRec :=
  (γs.hist, γs.done, γs.ep, γs.sn, γs.sw, γs.lk, γs.ok, γs.ak, γs.cb, γs.bd, γs.cap, γs.cert)

theorem MemStorNames.rec_inj (γs1 γs2 : MemStorNames) (h : γs1.tuple = γs2.tuple) : γs1 = γs2 := by
  cases γs1; cases γs2
  simp only [MemStorNames.tuple, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
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

omit package_sem in
theorem memStorReg_agree (ms : Loc) (γs1 γs2 : MemStorNames) :
    ⊢ memStorReg (GF := GF) ms γs1 -∗ memStorReg ms γs2 -∗ ⌜γs1 = γs2⌝ := by
  unfold memStorReg
  iintro #H1 #H2
  icases ghostMapElem_agree _ _ _ _ _ _ $$ H1 H2 with %H
  ipureintro; exact MemStorNames.rec_inj _ _ H

/-- The raft `Storage` interface value holding the `*MemoryStorage` `ms`. -/
def memStorIface (ms : Loc) : Storage :=
  interface.mkOk (go.GoType.PointerType MemoryStorage.ty) #ms

include sem in
omit package_sem in
theorem memStorIface_inj (ms1 ms2 : Loc) : memStorIface ms1 = memStorIface ms2 → ms1 = ms2 := by
  intro h
  simp only [memStorIface, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
    true_and] at h
  exact go.intoVal_inj h

/-- The storage behind the interface value `st`: a registered `MemoryStorage`, owned at `σ`,
holding a snapshot once compacted (`is_Storage_MemoryStorage`'s premise; 2026-10-16, stage R8a,
D11). -/
def memOwnStorage (st : Storage) (σ : StorState) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    ownMemoryStorage ms γs σ ∗ ⌜σ.prev.index' ≠ W64 0 → σ.ss.index' ≠ W64 0⌝)

/-- The right to append `p` to the storage `st` at `σ`: the `MemoryStorage`'s, of its names. -/
def memStorAppendTok (st : Storage) (σ : StorState) (p : List EntryM) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    memAppendTok ms γs σ p)

/-- The receipt of the append. -/
def memStorAppendedTok (st : Storage) (σ : StorState) (p : List EntryM) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    memAppendedTok ms γs σ p)

/-- (D19i part 1) The storage's boundary has reached `n`: the `MemoryStorage`'s, of its names. -/
def memStorCutI (st : Storage) (n : Int) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    memStorCut γs n)

/-- (D19i part 1) The floor's witness: the `MemoryStorage`'s, of its names. -/
def memStorFloorI (st : Storage) (x : w64) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    memFloorTok ms γs x)

/-- (2026-10-19, D21 M3) The storage's cap is at most `k`: the `MemoryStorage`'s, of its names. -/
def memStorCapI (st : Storage) (k : Int) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    ⌜γs.cap ≤ k⌝)

omit package_sem in
theorem memStorCut_capI (st : Storage) (n k : Int) :
    memStorCutI (GF := GF) st n ∗ memStorCapI st k ⊢ ⌜n ≤ k⌝ := by
  unfold memStorCutI memStorCapI
  iintro ⟨⟨%ms, %γs, %Hst, #Hreg, Hc⟩, ⟨%ms', %γs', %Hst', #Hreg', %Hk⟩⟩
  rw [Hst] at Hst'
  have := memStorIface_inj (GF := GF) _ _ Hst'
  subst this
  icases memStorReg_agree ms γs γs' $$ Hreg Hreg' with %H
  subst H
  icases memStorCut_cap γs n $$ Hc with %Hn
  ipureintro; omega

/-- (D22 S-b′2) The snapshot `k` is certified in the storage's registry: the `MemoryStorage`'s, of
its names. -/
def memStorCertI (st : Storage) (k : SnapTrip) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    memStorCert γs k)

/-- (2026-10-28, stage U4a) The terms the owner vouched for: the `MemoryStorage`'s, of its names. -/
def memStorTermsI (st : Storage) (ts : List w64) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    memTermsAt γs ts)

omit package_sem in
/-- (stage U4a) The owner vouches for the terms within its hold (`memStorage_terms`; within its
floor until stage U8). -/
theorem memStorTermsI_intro (st : Storage) (σ : StorState) (ts : List w64)
    (Hp : σ.pend = []) (Hl : (ts.length : Int) ≤ uint.Z σ.hd) (Ht : TermsOn σ ts) :
    memOwnStorage (GF := GF) st σ ⊢ |==> (memOwnStorage st σ ∗ memStorTermsI st ts) := by
  unfold memOwnStorage
  iintro ⟨%ms, %γs, %Hst, #Hreg, Hown, %Hne⟩
  icases memStorage_terms ms γs σ ts Hp Hl Ht $$ Hown with ⟨Hown, #Htm⟩
  imodintro
  isplitl [Hown]
  · iexists ms, γs
    iframe Hreg Hown
    ipureintro; exact ⟨Hst, Hne⟩
  unfold memStorTermsI
  iexists ms, γs
  iframe Hreg Htm
  ipureintro; exact Hst

/-- (2026-10-29, stage U8) The terms the owner vouched for before an append: the `MemoryStorage`'s,
of its names. -/
def memStorTermsPreI (st : Storage) (ts : List w64) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames), ⌜st = memStorIface ms⌝ ∗ memStorReg ms γs ∗
    memTermsPre γs ts)

omit package_sem in
/-- (stage U8) The owner vouches for the terms its view will have, its batch appended
(`memStorage_termsPre`). -/
theorem memStorTermsPreI_intro (st : Storage) (σ : StorState) (ts : List w64)
    (Hl : (ts.length : Int) ≤ uint.Z σ.hd) (Ht : TermsOn (storAbsorb σ) ts) :
    memOwnStorage (GF := GF) st σ ⊢ |==> (memOwnStorage st σ ∗ memStorTermsPreI st ts) := by
  unfold memOwnStorage
  iintro ⟨%ms, %γs, %Hst, #Hreg, Hown, %Hne⟩
  icases memStorage_termsPre ms γs σ ts Hl Ht $$ Hown with ⟨Hown, #Htm⟩
  imodintro
  isplitl [Hown]
  · iexists ms, γs
    iframe Hreg Hown
    ipureintro; exact ⟨Hst, Hne⟩
  unfold memStorTermsPreI
  iexists ms, γs
  iframe Hreg Htm
  ipureintro; exact Hst

omit package_sem in
/-- (stage U8) The receipt of an append makes them the storage's (`memTermsAt_receipt`). -/
theorem memStorTermsI_receipt (st : Storage) (ts : List w64) (σ : StorState) (p : List EntryM) :
    memStorTermsPreI (GF := GF) st ts ∗ memStorAppendedTok st σ p ⊢
      |==> (memStorAppendedTok st σ p ∗ memStorTermsI st ts) := by
  unfold memStorTermsPreI memStorAppendedTok
  iintro ⟨⟨%ms, %γs, %Hst, #Hreg, #Hpre⟩, ⟨%ms', %γs', %Hst', #Hreg', Ht⟩⟩
  rw [Hst] at Hst'
  have := memStorIface_inj (GF := GF) _ _ Hst'
  subst this
  icases memStorReg_agree ms γs γs' $$ Hreg Hreg' with %H
  subst H
  icases memTermsAt_receipt ms γs ts σ p $$ Hpre Ht with ⟨Ht, #Hta⟩
  imodintro
  isplitl [Ht]
  · iexists ms, γs
    iframe Hreg Ht
    ipureintro; exact Hst
  unfold memStorTermsI
  iexists ms, γs
  iframe Hreg Hta
  ipureintro; exact Hst

/-- The storage model of an application whose `Storage`s are bare `MemoryStorage`s. -/
instance memStorageModel : StorageModel GF where
  ownStorage := memOwnStorage
  appendTok := memStorAppendTok
  appendedTok := memStorAppendedTok
  storCut := memStorCutI
  storCut_persistent := fun st n => by unfold memStorCutI; infer_instance
  storFloor := memStorFloorI
  storFloor_persistent := fun st x => by unfold memStorFloorI; infer_instance
  storCap := memStorCapI
  storCap_persistent := fun st k => by unfold memStorCapI; infer_instance
  storCut_cap := memStorCut_capI
  storCert := memStorCertI
  storCert_persistent := fun st k => by unfold memStorCertI; infer_instance
  storTermsAt := memStorTermsI
  storTermsAt_persistent := fun st ts => by unfold memStorTermsI; infer_instance
  storTermsAt_intro := memStorTermsI_intro
  storTermsPre := memStorTermsPreI
  storTermsPre_persistent := fun st ts => by unfold memStorTermsPreI; infer_instance
  storTermsPre_intro := memStorTermsPreI_intro
  storTermsAt_receipt := memStorTermsI_receipt

omit package_sem in
theorem memStorCert_at (ms : Loc) (γs : MemStorNames) (k : SnapTrip) :
    ⊢ memStorReg (GF := GF) ms γs -∗ storCert (memStorIface ms) k -∗ memStorCert γs k := by
  iintro #Hreg Hc
  ihave Hc : memStorCertI (memStorIface ms) k $$ [Hc]
  · iexact Hc
  unfold memStorCertI
  icases Hc with ⟨%ms', %γs', %Hst, #Hreg', Hc⟩
  have := memStorIface_inj (GF := GF) _ _ Hst
  subst this
  icases memStorReg_agree ms γs γs' $$ Hreg Hreg' with %H
  subst H
  iexact Hc

omit package_sem in
theorem memStorCert_intro (ms : Loc) (γs : MemStorNames) (k : SnapTrip) :
    ⊢ memStorReg (GF := GF) ms γs -∗ memStorCert γs k -∗ storCert (memStorIface ms) k := by
  iintro #Hreg Hc
  ihave H : memStorCertI (memStorIface ms) k $$ [Hc]
  · unfold memStorCertI
    iexists ms, γs
    iframe Hreg Hc
    ipureintro; rfl
  iexact H

omit package_sem in
/-- (2026-10-19, D21 M3) A registered `MemoryStorage` at a cap at most `k` is capped at `k`. -/
theorem memStorCap_intro (ms : Loc) (γs : MemStorNames) (k : Int) (h : γs.cap ≤ k) :
    ⊢ memStorReg (GF := GF) ms γs -∗ storCap (memStorIface ms) k := by
  iintro #Hreg
  ihave H : memStorCapI (GF := GF) (memStorIface ms) k $$ []
  · unfold memStorCapI
    iexists ms, γs
    iframe Hreg
    ipureintro; exact ⟨rfl, h⟩
  iexact H

theorem memStorTerms_at (ms : Loc) (γs : MemStorNames) (ts : List w64) :
    ⊢ memStorReg (GF := GF) ms γs -∗ storTermsAt (memStorIface ms) ts -∗ memTermsAt γs ts := by
  iintro #Hreg Hc
  ihave Hc : memStorTermsI (memStorIface ms) ts $$ [Hc]
  · iexact Hc
  unfold memStorTermsI
  icases Hc with ⟨%ms', %γs', %Hst, #Hreg', Hc⟩
  have := memStorIface_inj (GF := GF) _ _ Hst
  subst this
  icases memStorReg_agree ms γs γs' $$ Hreg Hreg' with %H
  subst H
  iexact Hc

theorem memStorFloor_at (ms : Loc) (γs : MemStorNames) (x : w64) :
    ⊢ memStorReg (GF := GF) ms γs -∗ storFloor (memStorIface ms) x -∗ memFloorTok ms γs x := by
  iintro #Hreg Hc
  ihave Hc : memStorFloorI (memStorIface ms) x $$ [Hc]
  · iexact Hc
  unfold memStorFloorI
  icases Hc with ⟨%ms', %γs', %Hst, #Hreg', Hc⟩
  have := memStorIface_inj (GF := GF) _ _ Hst
  subst this
  icases memStorReg_agree ms γs γs' $$ Hreg Hreg' with %H
  subst H
  iexact Hc

/-! ### The conversions, under the registry's record -/

theorem memStorAppendTok_at (ms : Loc) (γs : MemStorNames) (σ : StorState) (p : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ appendTok (memStorIface ms) σ p -∗ memAppendTok ms γs σ p := by
  iintro #Hreg Ht
  ihave Ht : memStorAppendTok (memStorIface ms) σ p $$ [Ht]
  · iexact Ht
  unfold memStorAppendTok
  icases Ht with ⟨%ms', %γs', %Hst, #Hreg', Ht⟩
  have := memStorIface_inj (GF := GF) _ _ Hst
  subst this
  icases memStorReg_agree ms γs γs' $$ Hreg Hreg' with %H
  subst H
  iexact Ht

theorem memStorAppendedTok_intro (ms : Loc) (γs : MemStorNames) (σ : StorState)
    (p : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ memAppendedTok ms γs σ p -∗
      appendedTok (memStorIface ms) σ p := by
  iintro #Hreg Ht
  ihave H : memStorAppendedTok (memStorIface ms) σ p $$ [Ht]
  · unfold memStorAppendedTok
    iexists ms, γs
    iframe Hreg Ht
    ipureintro; rfl
  iexact H

/-- What a `Ready` hands out for its entries (`appendRight`, `InvStorage.lean`), at the
`MemoryStorage`: nothing for no entries, otherwise `MemoryStorage.Append`'s token. -/
theorem memAppendRight_at (ms : Loc) (γs : MemStorNames) (p : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ appendRight (memStorIface ms) p -∗
      ⌜p = []⌝ ∨ ∃ σ, memAppendTok ms γs σ p := by
  iintro #Hreg Hr
  unfold appendRight
  icases Hr with (%Hp | ⟨%σ, Ht⟩)
  · ileft; ipureintro; exact Hp
  iright
  iexists σ
  iapply memStorAppendTok_at ms γs σ p $$ Hreg Ht

/-- ... and the receipt the application gives back (`appendReceipt`). -/
theorem memAppendReceipt_intro (ms : Loc) (γs : MemStorNames) (p : List EntryM) :
    ⊢ memStorReg (GF := GF) ms γs -∗ (⌜p = []⌝ ∨ ∃ σ, memAppendedTok ms γs σ p) -∗
      appendReceipt (memStorIface ms) p := by
  iintro #Hreg Hr
  unfold appendReceipt
  icases Hr with (%Hp | ⟨%σ, Ht⟩)
  · ileft; ipureintro; exact Hp
  iright
  iexists σ
  iapply memStorAppendedTok_intro ms γs σ p $$ Hreg Ht

/-! ### The contract and the application's `Append` -/

/-- **The application's `Append`** of the entries a `Ready` handed out, in the contract's terms:
the right in (`appendRight`, `RawNode.Ready`'s), the receipt out (`appendReceipt`, what
`node.Advance` takes back), the slice of read-only entries lent. Under `MemoryStorage.Append`'s
premise, which is the caller's to establish (the register checks it in Go, `fits`; etcd's
server derives it from a `Ready`'s `readyIdx` and the time-receipt bound, `rnLogFits`): the batch's last index is at most
`2^61`, i.e. `e0.Index + |p| ≤ 2^61` for its first entry `e0`. -/
theorem memStorage_Append (ms : Loc) (γs : MemStorNames) (p : List EntryM) (s : GoSlice)
    (dq : DFrac)
    (Hfit : ∀ e0, p.head? = some e0 → uint.Z e0.Index' + (p.length : Int) ≤ 2^61) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
        memStorReg ms γs ∗ appendRight (memStorIface ms) p ∗ entsPts s dq p }}
      (App (Val (ms @!! go.GoType.PointerType MemoryStorage.ty @!! go!"Append")) (Val #s))
    {{ RET #interface.nil; appendReceipt (memStorIface ms) p ∗ entsPts s dq p }} := by
  iintro %Φ ⟨#Hinit, #Hreg, Hr, Hs⟩ HΦ
  ihave Hr := memAppendRight_at ms γs p $$ Hreg Hr
  icases Hr with (%Hp | ⟨%σ, Ht⟩)
  · ihave Htok : (⌜p = []⌝ ∨ memAppendTok ms γs memStorEmpty p : IProp GF) $$ []
    · ileft; ipureintro; exact Hp
    wp_apply MemoryStorage.wp_Append ms γs memStorEmpty p s dq Hfit $$ [$Hinit $Htok $Hs]
      as ⟨Hrec, Hs⟩
    iapply HΦ
    iframe Hs
    iapply memAppendReceipt_intro ms γs p $$ Hreg
    ileft; ipureintro; exact Hp
  ihave Htok : (⌜p = []⌝ ∨ memAppendTok ms γs σ p : IProp GF) $$ [Ht]
  · iright; iexact Ht
  wp_apply MemoryStorage.wp_Append ms γs σ p s dq Hfit $$ [$Hinit $Htok $Hs] as ⟨Hrec, Hs⟩
  iapply HΦ
  iframe Hs
  iapply memAppendReceipt_intro ms γs p $$ Hreg
  icases Hrec with (%Hp | Hrec)
  · ileft; ipureintro; exact Hp
  iright
  iexists σ
  iexact Hrec

end model

section certLink
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [MemStorReg GF]

/-- A registered `MemoryStorage` whose registry is tied to `γ` meets `storCertOk γ`. -/
theorem memStorCertOk_intro (γ : RaftNames) (ms : Loc) (γs : MemStorNames) :
    ⊢ memCertInv (GF := GF) γ γs -∗ memStorReg ms γs -∗ storCertOk γ (memStorIface ms) := by
  iintro #Hinv #Hreg
  unfold storCertOk
  isplit
  · iintro !> %k %E %hE #Hc
    ihave #Hc := memStorCert_at ms γs k $$ Hreg Hc
    iapply memCert_read γ γs k E hE $$ Hinv Hc
  · iintro !> %k %E %hE #Hk
    imod memCert_register γ γs k E hE $$ Hinv Hk with #Hc
    imodintro
    iapply memStorCert_intro ms γs k $$ Hreg Hc

end certLink

end EtcdGrove
end Perennial
