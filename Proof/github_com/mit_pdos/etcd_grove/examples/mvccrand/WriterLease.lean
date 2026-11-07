/-
The writer's lessor resources (`writer.grant`, `writer.revoke`, `writer.checkLeases`,
`examples/mvccrand/mvccrand.go`). Lean-first (no Rocq counterpart).

`writerOwn` (`Writer.lean`) holds what the store's puts and deletes share with the lessor: the
model's live leases `Lm`, the lease owner's resource `leaseOwn (mvccLeases γ.kv) L I` at the store's
item map. **`writerLe`** holds the rest of the lessor, which only the writer's lease operations use:

- the lessor `lp` behind the writer's `le` field (`wv.le' = lessorIface lp`), its invariant, its
  configuration, the grant guard at `True` (so every id is `leaseGranted`), its mode not monotone
  (`lessorRevocable`, which `Revoke` takes; `NewLessor` at `mono = false`), its backend's contract
  for the lessor's writes (`lessorBackend`, `Grant`'s record put) at the writer's hook `f` and the
  batch lock's invariant `True` (the tester's backend has none), the part a write lends being the
  writer's half of `le.b` (`lessorBeOn`, which `Grant` gives back), the tracked buckets' right the
  put takes being the lease bucket's part (`rbPart`): all persistent, `writerLeRO`;
- a reader slot of the lessor's lock (`Lookup`, `GetLease`), its revokers at `L`, the ids it ever
  granted `U` (`leaseEver`, which `Grant` extends: each at most `nextID`, so `nextID + 1` is new);
- the backend contract's lent share `R` (each write gives it back) and a supply of `k` write
  tokens `T` (each `Grant` spends one);
- what `Revoke` needs beyond the store's handle: the range deleter's owner `rdOwn` at the store's
  deleter (`mvccDeleter`), the lessor's user half of its `le.b` (`lessorBeOn`, at the store's
  backend `B.be`), the lease bucket's part of the tracked buckets (`rbPart`, which `Grant`'s put
  also takes), the lease bucket's parameters (`leaseParams`);
- the writer's `nextID` field at `n` (`0 ≤ n`), every live lease's id in `(0, n]` (so `nextID + 1`
  is never live and no live lease is `0`).

The write tokens are abstract (`T`, `R`): `runChecks` picks them, from `NewLessor`'s
`lessorApplyOk` (`T` a write-back token, `R` the reader's open share; its lent part `Ln` the lens
`rwLens (lessorBeOn lp be) (lessorBeOn lp be)`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Writer
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section model
variable [GooseExts]

/-- **The tester's test of a key on the lease `id`** in the map `M` (`ok && e.lease == id`). -/
def onLease (M : GMap GoString kvRec) (id : w64) (k : GoString) : Bool :=
  match M !! k with
  | some e => decide (e.lease' = id)
  | none => false

/-- **The tester's lease of a key** in the map `M` (`0` for none). -/
def leaseOfM (M : GMap GoString kvRec) (k : GoString) : w64 :=
  match M !! k with
  | some e => e.lease'
  | none => W64 0

/-- The last revision's state of the writer's history is the store's state after its log. -/
theorem lastSt_match (L : Log) (Hs : List HRev) (hlen : Hs.length = L.length)
    (hrev : ∀ r < Hs.length, ∃ e, Hs[r]? = some e ∧ revOk L Hs r e) :
    stMatch (lastSt Hs) (stateAfter L) := by
  by_cases h0 : Hs.length = 0
  · have hL : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hH : Hs = [] := List.eq_nil_of_length_eq_zero h0
    subst hL hH
    refine ⟨fun k => ?_, fun v hv => ?_⟩
    · simp [lastSt, stateAfter, findKey]
    · simp [stateAfter] at hv
  · obtain ⟨e, he, hst, -⟩ := hrev (Hs.length - 1) (by omega)
    have hl : lastSt Hs = e.1 := by unfold lastSt; rw [he]; rfl
    rw [hl]
    have hs : stateAt L (Hs.length - 1) = stateAfter L := by
      unfold stateAt; rw [show Hs.length - 1 + 1 = L.length by omega, List.take_length]
    rw [← hs]; exact hst

/-- **`GetLease` of a key is the tester's lease of it** (the store's item map of a state the map
`M` matches). -/
theorem leaseGet_eq (M : GMap GoString kvRec) (s : List EtcdKv) (hM : stMatch M s) (k : GoString) :
    ((leaseItemsOf s).lookup (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk k)).getD (W64 0) =
      leaseOfM M k := by
  rw [leaseItemsOf_lookup]
  simp only
  rw [hM.1 k]
  unfold leaseOfM
  cases M !! k with
  | none => rfl
  | some e =>
    simp only [Option.map_some, Option.bind_some, kvLease, kvOfRec]
    by_cases h : e.lease' = W64 0
    · simp [h]
    · have h' : (e.lease' = W64 0) = False := eq_false h
      simp only [h', ↓reduceIte]; rfl

/-- **The keys the store's item map puts on a live lease `id` (not `0`) are the tester's keys on
it, in its order** (a sorted state the map `M` matches): `Revoke`'s deletions and `Keys()` sorted
are the tester's `ks` and `want`. -/
theorem leaseDelKeys_eq_onLease (M : GMap GoString kvRec) (s : List EtcdKv) (hM : stMatch M s)
    (hs : s.Pairwise etcdKvLess) (id : w64) (hid : id ≠ W64 0) :
    leaseDelKeys s id = keyList.filter (onLease M id) := by
  apply eq_of_lt_sorted_mem (leaseDelKeys_sorted hs id) (keyList_sorted.filter _)
  intro x
  rw [leaseDelKeys_mem hs id x, leaseItemsOf_lookup, List.mem_filter]
  simp only
  rw [hM.1 x]
  unfold onLease
  cases hx : M !! x with
  | none => simp
  | some e =>
    simp only [Option.map_some, Option.bind_some, kvLease, kvOfRec, decide_eq_true_eq]
    have hk : x ∈ keyList := by
      have hf := hM.1 x
      rw [hx] at hf
      have hm := List.mem_of_find?_eq_some hf
      have hkk := findKey_key hf
      simp only [kvOfRec] at hkk
      have := hM.2 _ hm
      simp only [kvOfRec] at this
      exact this
    by_cases h : e.lease' = W64 0
    · simp only [h, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro _ h'; exact hid h'.symm
    · simp only [h, ↓reduceIte, Option.some.injEq, hk, true_and]

/-- The keys the store's item map puts on `id` are among the tester's keys. -/
theorem leaseKeys_sub (M : GMap GoString kvRec) (s : List EtcdKv) (hM : stMatch M s)
    (id : w64) (k : GoString)
    (h : (leaseItemsOf s).lookup (go_etcd_io.etcd.server.v3.lease.LeaseItem.mk k) = some id) :
    k ∈ keyList := by
  rw [leaseItemsOf_lookup] at h
  simp only at h
  cases hf : findKey k s with
  | none => rw [hf] at h; cases h
  | some kv =>
    have := hM.2 kv (List.mem_of_find?_eq_some hf)
    rwa [findKey_key hf] at this

end model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The writer's lessor, persistently** (see the file header). -/
def writerLeRO (wv : writer) (γ : RandNames) (B : KBReal) (f : GoFunc) (lp : Loc) (T R : IProp GF) :
    IProp GF :=
  iprop(⌜wv.le' = lease.lessorIface lp⌝ ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
    lease.lessorInv lp (mvccLeases γ.kv) ∗ lease.lessorCfg lp ∗
    lease.lessorGuard (mvccLeases γ.kv) (fun _ => iprop(True)) ∗
    lease.lessorRevocable (mvccLeases γ.kv) ∗
    lease.lessorBackend lp iprop(True) #f T (lease.lessorBeOn lp B.be) R
      (backend.rbPart B.γB (· = leaseName)))

instance writerLeRO_persistent (wv : writer) (γ : RandNames) (B : KBReal) (f : GoFunc) (lp : Loc)
    (T R : IProp GF) : Persistent (writerLeRO (GF := GF) wv γ B f lp T R) := by
  unfold writerLeRO; infer_instance

/-- **The writer's lessor resources** (see the file header), at the live leases `L`, the writer's
`nextID` at `n` and `k` write tokens left. -/
def writerLe (w : Loc) (wv : writer) (γ : RandNames) (B : KBReal) (f : GoFunc) (L : List w64)
    (n : w64) (k : Nat) (T R : IProp GF) : IProp GF :=
  iprop(∃ (lp : Loc) (rd : GoFunc) (r : GMap GoString backend.BktData) (U : List w64),
    writerLeRO wv γ B f lp T R ∗
    lease.lessorRd lp (mvccLeases γ.kv) ∗ lease.leaseRevokers (mvccLeases γ.kv) L ∗
    lease.leaseEver (mvccLeases γ.kv) U ∗
    R ∗ ([∗list] _x ∈ List.replicate k (), T) ∗
    lease.rdOwn (mvccLeases γ.kv) rd ∗ mvccDeleter rd γ.kv ∗ lease.lessorBeOn lp B.be ∗
    backend.rbPart B.γB (· = leaseName) r ∗ ⌜leaseParams B.P⌝ ∗
    wF go!"nextID" w ↦ n ∗
    ⌜0 ≤ sint.Z n ∧ (∀ id ∈ L, 0 < sint.Z id ∧ sint.Z id ≤ sint.Z n) ∧
      ∀ id ∈ U, sint.Z id ≤ sint.Z n⌝)

/-- **The published revision is positive** (the tester's invariant): so the writer's history has
at least two revisions. -/
theorem writer_pub_pos (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (h : Loc)
    (γ : RandNames) (p : w64) :
    inv worldN (worldInv h γ) ∗ ghostVar γ.pv (1 : Qp).half p ⊢
      |={⊤}=> ghostVar γ.pv (1 : Qp).half p ∗ ⌜1 ≤ sint.Z p⌝ := by
  haveI := fun σ => hpers.2.2.2.2.2.1 γ.kv σ
  haveI := fun S => hpers.2.2.2.2.2.2.1 γ.ws S
  haveI : Timeless (worldInv (GF := GF) h γ) := by unfold worldInv; infer_instance
  iintro ⟨#Hinv, Hp⟩
  iinv Hinv with >Hi Hclose
  iunfold worldInv at Hi
  icases Hi with ⟨%σ, %S, %p', %Hl, %W, Hσ, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, Hlb, %Hok⟩
  ihave %Hag := ghostVar_agree γ.pv _ _ _ _ $$ Hpv Hp
  imod Hclose $$ [Hσ Hgσ HS Hreg Hpub Hpv Hpm Hlb] with -
  · inext; iunfold worldInv; iexists σ, S, p', Hl, W; iframe; ipureintro; exact Hok
  imodintro
  iframe Hp
  ipureintro
  rw [← Hag]; exact Hok.2.1

/-- Every id is granted by the writer's lessor (its guard is `True`). -/
theorem leaseGranted_of_guard (γl : GName) (id : w64) :
    lease.lessorGuard (GF := GF) γl (fun _ => iprop(True)) ⊢ lease.leaseGranted γl id := by
  iintro #Hg
  iunfold lease.leaseGranted
  iexists (fun _ => iprop(True))
  iframe Hg
  iintro !>
  itrivial

end defs

end mvccrand
end EtcdGrove
end Perennial
