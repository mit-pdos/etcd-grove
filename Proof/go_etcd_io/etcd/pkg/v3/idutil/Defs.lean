/-
`pkg/idutil` (the request id generator): the shared vocabulary of its specs (`NewGenerator`,
`Generator.Next`), used by the server's request path (`etcdserver/InvRequest.lean`) and the wait
registry (`wait/Defs.lean`: an id's wait slot). Lean-first (no Rocq counterpart); moved here from
the server's `InvRequest.lean` (unit 0 of the request path) in unit 2 (2026-10-12).

**Unique ids** (`idGen`, `idFresh`, `idClaim`): `Generator.Next` returns `prefix |
lowbit(suffix, 48)` for an atomically incremented `suffix`: `2 ^ 48` consecutive calls return
distinct ids. `Next` returns an id nobody holds (`idFresh γi id`: the right to claim the id for a request's data,
`idClaim γi id d` (persistent, agreeing), and the id's slot in the wait registry, `idSlot`).
**The lifetime bound from time receipts** (D19b, 2026-10-18; `notes/decisions.md`): the
generator's invariant holds one time receipt per id issued (`⧗ k` for `k` ids; Perennial's
`GooseLang/Receipts.lean`), and `Next` takes one more from the Go step of its `atomic.AddUint64`
(`wp_AddUint64_receipt`), so `k + 1 < receiptBound GF`: under the pure fact `receiptBound GF ≤
2 ^ 48` (which the adequacy theorem discharges by its choice of the step bound `N`) a process
issues fewer than `2 ^ 48` ids (the suffix wraps after that). `idCred γi n` is that pure fact
(`γi` and `n` unused, kept so the statements over `idCred` keep their form). History: until D17
(2026-10-17) `idCred γi n` was `n` exclusive credits of the `2 ^ 48 - 1` `NewGenerator` handed
out, unsatisfiable against the unbounded supply the request path and read loop need (`□ |==>
idCred ρ.ids 1`); from D17 to D19b it was `idLifeBound`, a persistent premise over the
generator's own ghost counter, refutable as a hypothesis of a closed theorem (D19a).

**One claims map for the cluster** (D21e (A), stage M4, 2026-10-19): the issued ids' map and the
claimers' facts are the cluster's (`idClusterInv`, allocated once, `idCluster_alloc`), keyed by the
full id; each member's generator issues under its prefix (`uint16(memberID) << 48`), recording
its issued ids at its prefix's entry of a second cluster map (`γi.cnt`), whose element it owns
(`idShare`), so that the cluster's map holds the reserved `0` and exactly the ids the members
issued. Request ids are unique across members only if the prefixes differ
(`nonissues/etcd-request-id-member-prefix.md`): the allocation's pure premise (`idPfxOk` of each
member's prefix, the prefixes `Nodup`), the only premise this adds. The claimers' facts are per
prefix (`Φs`, the cluster's choice; a member's own `Φs γi.pfx`): a member reads the claimer's
fact of an id of its own prefix only (`idClaim_fact`). The wait slots stay the member's.

**A claim's ghost name** (the vertical slice's unit V2, 2026-10-14): a claim records, besides the
data, a ghost name `γf` the claimer chose, and the generator's invariant holds, for every claim,
the claimer's persistent fact `Φ id d γf` (`idGen γi g Φ`, `Φ` fixed at `NewGenerator`): the way a
proposer hands the apply thread, which knows of the request only its committed data and their
claim, what it knew when it proposed (the server's `Φ`: the certificate of a log the proposer's
client had seen, `srvFloorFact`, `etcdserver/InvRequest.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.DGhostVar
public import Perennial.GooseLang.Receipts
public import GooseLang.Ext.IdIssue.Specs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- The id generators' ghost names (D21e (A), stage M4, 2026-10-19): the cluster's issued ids'
map (keyed by id: the data an id was claimed for, `none` until claimed) and its prefixes' map
(keyed by a member's prefix: the ids that member issued), the member's wait slots (keyed by id)
and the member's prefix. (Until M4 one generator owned the issued map; until D19b, 2026-10-18,
also the issued ids' counter, `cred`.) Since 2026-10-20 (linkv-txn stage B1) also the cluster's
registries' map (keyed by a member's prefix: the ghost name of that member's wait registry, `none`
until its `start` made it; `idWaitTok`, `idWaitIs`). -/
structure IdNames where
  issued : GName
  cnt : GName
  slot : GName
  pfx : w64
  wn : GName
  /-- (R2c, 2026-11-02) the incarnation's number: `0` for a member's first start -/
  inc : Nat
  /-- (R2c) the cluster's keys' facts map (keyed by key: the parameter of the cluster's facts) -/
  fs : GName
  /-- (R2c stage 2) the incarnation's pending ids (counted by `Next`'s increment, not yet issued) -/
  pend : GName
  /-- (etcd-dist D7, 2026-11-23) the cluster's map of each prefix's names (`idPfxTok`, `idPfxInv`):
  its ids' map (each id's issuer, tagged with its incarnation since T10 B6, 2026-11-26), kept on the
  prefix's member's machine -/
  gen : GName

/-- **A member incarnation's key** (R2c, 2026-11-02, `notes/restart-plan.md`): its prefix and its
incarnation number. The cluster's id state is per key: each incarnation has its own list of issued
ids, its own registry cell and its own claims' facts. -/
abbrev IdKey := w64 × Nat

/-- The incarnation's key. -/
abbrev IdNames.key (γi : IdNames) : IdKey := (γi.pfx, γi.inc)

/-- **A claim** (an entry of the issued ids' map, once claimed; R2c): the request's data, the
claimer's ghost name and the claimer's key. -/
abbrev IdClaimV := List w8 × GName × IdKey

/-- `id` is among the first `k` ids of the generator with prefix `pfx` and initial suffix
`s0`: `pfx | lowbit(s0 + j, 48)` for `1 ≤ j ≤ k`. -/
def idIssued (pfx s0 : w64) (k : Nat) (id : w64) : Prop :=
  ∃ j : Nat, 1 ≤ j ∧ j ≤ k ∧ id = pfx ||| ((s0 + W64 (j : Int)) &&& W64 (2 ^ 48 - 1))

/-- **An id's prefix**: its 16 high bits (D21e (A)). -/
def idPfx (id : w64) : w64 := id &&& W64 (2 ^ 64 - 2 ^ 48)

/-- **A member's prefix** (`NewGenerator`'s `uint64(memberID) << 48`). -/
def idPfxOf (m : w16) : w64 := W64 (uint.Z m) <<< W64 48

/-- **A good member prefix** (D21e (A)): not `0` (D19c: a generator of prefix `0` issues the id
`0` of raft's bootstrap conf changes, `nonissues/etcd-request-id-zero-bootstrap-confchange.md`), its
48 low bits `0`. -/
def idPfxOk (p : w64) : Prop := p ≠ W64 0 ∧ p &&& W64 (2 ^ 48 - 1) = W64 0

/-- The prefix of an id under a prefix with no low bits is that prefix. -/
theorem idPfx_or (pfx x : w64) (h : pfx &&& W64 (2 ^ 48 - 1) = W64 0) :
    idPfx (pfx ||| (x &&& W64 (2 ^ 48 - 1))) = pfx := by
  unfold idPfx
  have e1 : W64 (2 ^ 48 - 1) = 0xffffffffffff#64 := rfl
  have e2 : W64 (2 ^ 64 - 2 ^ 48) = 0xffff000000000000#64 := rfl
  have e3 : W64 0 = 0#64 := rfl
  rw [e1, e3] at h; rw [e1, e2]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun v => v.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ofNat] at hb ⊢
  have e2 : (0xffff000000000000 : Nat).testBit i = decide (48 ≤ i) := by
    rw [show (0xffff000000000000 : Nat) = (2 ^ 16 - 1) * 2 ^ 48 by rfl, Nat.testBit_mul_two_pow,
      Nat.testBit_two_pow_sub_one]
    by_cases h48 : 48 ≤ i <;> simp [h48] <;> omega
  have e1 : (0xffffffffffff : Nat).testBit i = decide (i < 48) := by
    rw [show (0xffffffffffff : Nat) = 2 ^ 48 - 1 by rfl, Nat.testBit_two_pow_sub_one]
  by_cases h48 : i < 48
  · have h48' : ¬ 48 ≤ i := by omega
    simp [e1, hi, h48] at hb
    simp [e2, h48']
    rw [BitVec.getLsbD_eq_getElem hi]; exact hb
  · simp [e1, e2, hi, h48]; omega

/-- An id of a prefix that is not `0` is not `0`. -/
theorem idutil_or_ne_zero (pfx x : w64) (h : pfx ≠ W64 0) : pfx ||| x ≠ W64 0 := by
  intro h'
  apply h
  have := congrArg (fun y : w64 => pfx &&& y) h'
  simp only [BitVec.and_or_distrib_left, BitVec.and_self] at this
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat this
  rw [BitVec.toNat_or] at h1
  simp only [BitVec.toNat_and] at h1
  have : (W64 0).toNat = 0 := rfl
  rw [this] at h1 ⊢
  simp only [Nat.and_zero] at h1
  exact Nat.eq_zero_of_le_zero (h1 ▸ Nat.left_le_or)

/-- The generator's invariant's namespace. -/
def idN : Namespace := nroot .@ "idutil"

/-- The cluster's claims invariant's namespace (D21e (A)). -/
def idClusterN : Namespace := nroot .@ "idutil_cluster"

@[simp] theorem idClusterN_idN : (↑idClusterN : CoPset) ⊆ ⊤ \ ↑idN :=
  mask_ndot_ne' nroot "idutil_cluster" "idutil" (by decide)

/-- The `n` low bits of `x`, as a number. -/
theorem idutil_mask_toNat (x : BitVec 64) (n : Nat) (h : n ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ n - 1)).toNat = x.toNat % 2 ^ n := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have h1 : 2 ^ n - 1 < 2 ^ 64 := by
    have : 2 ^ n ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) h
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [Nat.mod_eq_of_lt h1, Nat.and_two_pow_sub_one_eq_mod]

theorem idutil_prefix_low (y : BitVec 64) : y <<< 48#64 &&& 0xffffffffffff#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  have := idutil_mask_toNat (y <<< 48#64) 48 (by omega)
  simp only [show (BitVec.ofNat 64 (2 ^ 48 - 1)) = 0xffffffffffff#64 from rfl] at this
  rw [this, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq]
  rw [show 48 % 2 ^ 64 = 48 from rfl, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    Nat.mul_mod_left]

/-- The prefix of a member id that is not `0` is not `0`. -/
theorem idutil_prefix_ne (m : w16) (h : m ≠ W16 0) : W64 (uint.Z m) <<< W64 48 ≠ W64 0 := by
  intro h'
  apply h
  have h1 := congrArg BitVec.toNat h'
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft] at h1
  have hm : m.toNat < 2 ^ 16 := m.isLt
  have e1 : (W64 (uint.Z m)).toNat = m.toNat := by
    unfold W64; simp only [BitVec.toNat_ofInt]; simp [uint.Z]; omega
  have e2 : (W64 48).toNat = 48 := rfl
  rw [e1, e2, Nat.shiftLeft_eq] at h1
  have e3 : (W64 0).toNat = 0 := rfl
  rw [e3] at h1
  apply BitVec.eq_of_toNat_eq
  have : (W16 0).toNat = 0 := rfl
  rw [this]
  omega

/-- A member's prefix as a number: its id's 16 low bits, shifted by 48. -/
theorem idPfxOf_toNat (m : w16) : (idPfxOf m).toNat = m.toNat * 2 ^ 48 := by
  unfold idPfxOf
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  have hm : m.toNat < 2 ^ 16 := m.isLt
  have e1 : (W64 (uint.Z m)).toNat = m.toNat := by
    unfold W64; simp only [BitVec.toNat_ofInt]; simp [uint.Z]; omega
  have e2 : (W64 48).toNat = 48 := rfl
  rw [e1, e2, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have : m.toNat * 2 ^ 48 < 2 ^ 16 * 2 ^ 48 := Nat.mul_lt_mul_of_pos_right hm (by omega)
  omega

/-- **The member ids' prefixes, good and distinct** (D21e (A)): from the pure premise that the
member ids' 16 low bits are distinct and not `0` (`nonissues/etcd-request-id-member-prefix.md`). -/
def idPfxsOf (ps : List w64) : List w64 := ps.map (fun id => idPfxOf (W16 (uint.Z id)))

theorem idPfxOf_low (id : w64) : uint.Z (W16 (uint.Z id)) = uint.Z id % 2 ^ 16 := by
  unfold W16; simp [uint.Z]

/-- A list's map is without duplicates if another map of it is, and the second map determines the
first on the list. -/
theorem idutil_nodup_map {α β γ : Type} (f : α → β) (g : α → γ) :
    ∀ (l : List α), (l.map f).Nodup → (∀ a ∈ l, ∀ b ∈ l, g a = g b → f a = f b) →
      (l.map g).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hnd, hinj => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd ⊢
    refine ⟨?_, idutil_nodup_map f g l hnd.2 (fun x hx y hy =>
      hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    rintro ⟨b, hb, hgb⟩
    exact hnd.1 ⟨b, hb, hinj b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) hgb⟩

/-- A list of distinct numbers below `n` has at most `n` elements. -/
theorem idutil_nodup_length_le : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < n) →
    l.length ≤ n
  | 0, [], _, _ => Nat.le_refl _
  | 0, x :: _, _, h => absurd (h x (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | n + 1, l, hnd, h => by
    have ih := idutil_nodup_length_le n (l.erase n) (hnd.erase n) (fun x hx => by
      have := (List.Nodup.mem_erase_iff hnd).1 hx
      have := h x this.2
      omega)
    rw [List.length_erase] at ih
    split at ih <;> omega

theorem idPfxsOf_ok (ps : List w64)
    (Hnd : (ps.map (fun id => uint.Z id % 2 ^ 16)).Nodup) (Hnz : ∀ id ∈ ps, uint.Z id % 2 ^ 16 ≠ 0) :
    (idPfxsOf ps).Nodup ∧ (∀ p ∈ idPfxsOf ps, idPfxOk p) ∧ ps.length ≤ 2 ^ 16 - 1 := by
  unfold idPfxsOf
  refine ⟨?_, ?_, ?_⟩
  · apply idutil_nodup_map _ _ ps Hnd
    intro a _ b _ h
    have h1 := congrArg BitVec.toNat h
    rw [idPfxOf_toNat, idPfxOf_toNat] at h1
    have h2 : (W16 (uint.Z a)).toNat = (W16 (uint.Z b)).toNat :=
      Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 ^ 48) h1
    have h3 : uint.Z (W16 (uint.Z a)) = uint.Z (W16 (uint.Z b)) := by
      simp only [uint.Z]; rw [h2]
    rw [idPfxOf_low, idPfxOf_low] at h3
    exact h3
  · intro p hp
    obtain ⟨id, hid, rfl⟩ := List.mem_map.1 hp
    refine ⟨idutil_prefix_ne _ ?_, idutil_prefix_low _⟩
    intro h
    apply Hnz id hid
    rw [← idPfxOf_low, h]; rfl
  · have hm : (ps.map (fun id => (uint.Z id % 2 ^ 16).toNat - 1)).Nodup := by
      apply idutil_nodup_map _ _ ps Hnd
      intro a ha b hb h
      have h1 := Hnz a ha
      have h2 := Hnz b hb
      have h3 : 0 ≤ uint.Z a % 2 ^ 16 := Int.emod_nonneg _ (by decide)
      have h4 : 0 ≤ uint.Z b % 2 ^ 16 := Int.emod_nonneg _ (by decide)
      omega
    have := idutil_nodup_length_le (2 ^ 16 - 1) _ hm (fun x hx => by
      obtain ⟨id, -, rfl⟩ := List.mem_map.1 hx
      have : uint.Z id % 2 ^ 16 < 2 ^ 16 := Int.emod_lt_of_pos _ (by decide)
      omega)
    simpa using this

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The right to ids** (what `Next` takes; since D19b the pure fact that the time-receipt
bound is at most `2 ^ 48`, whatever `γi` and `n`: see the file header). -/
def idCred (_γi : IdNames) (_n : Nat) : IProp GF := iprop(⌜receiptBound GF ≤ 2 ^ 48⌝)

instance idCred_persistent (γi : IdNames) (n : Nat) : Persistent (idCred (GF := GF) γi n) := by
  unfold idCred; infer_instance

/-- The supply of ids the server's request path and read loop use (`□ |==> idCred γi 1`), from
the bound on the time receipts. -/
theorem idCred_supply (γi : IdNames) (Hb : receiptBound GF ≤ 2 ^ 48) :
    ⊢ □ (|==> idCred (GF := GF) γi 1) := by
  istart
  imodintro
  imodintro
  iunfold idCred
  ipureintro
  exact Hb

end ghost

section ghostG1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The right to claim the id `id`** (exclusive). -/
def idUnclaimed (γi : IdNames) (id : w64) : IProp GF :=
  id ↪[γi.issued] (none : Option IdClaimV)

end ghostG1

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


end ghost

section ghostG1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The id `id` was claimed by this incarnation** for the data `d`, with the claimer's ghost name
`γf` (persistent; agreeing): the claim records the claimer's key (R2c, 2026-11-02). What the
proposer makes (`idClaim_make`) and a waiter of the incarnation holds. -/
def idClaim (γi : IdNames) (id : w64) (d : List w8) (γf : GName) : IProp GF :=
  id ↪[γi.issued]□ (some (d, γf, γi.key) : Option IdClaimV)

instance idClaim_persistent (γi : IdNames) (id : w64) (d : List w8) (γf : GName) :
    Persistent (idClaim (GF := GF) γi id d γf) := by
  unfold idClaim; infer_instance

/-- **The id `id` was claimed for `d`, with `γf`, by some incarnation** (persistent; R2c): what a
committed entry's reader knows, whoever proposed it. -/
def idClaimAny (γi : IdNames) (id : w64) (d : List w8) (γf : GName) : IProp GF :=
  iprop(∃ k : IdKey, id ↪[γi.issued]□ (some (d, γf, k) : Option IdClaimV))

instance idClaimAny_persistent (γi : IdNames) (id : w64) (d : List w8) (γf : GName) :
    Persistent (idClaimAny (GF := GF) γi id d γf) := by
  unfold idClaimAny; infer_instance

end ghostG1

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


/-- An incarnation's claim is a claim. -/
theorem idClaimAny_of (γi : IdNames) (id : w64) (d : List w8) (γf : GName) :
    idClaim (GF := GF) γi id d γf ⊢ idClaimAny γi id d γf := by
  unfold idClaim idClaimAny
  iintro #H
  iexists γi.key
  iexact H

end ghost

section ghostG3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **No request claims the id `0`** (persistent; D19c): the issued ids' map holds `0 ↦ none`,
read-only. The cluster's allocation gives it (`idCluster_alloc`, D21e (A); until stage M4
`NewGenerator`, for a member id whose 16 low bits are not `0`). -/
def idNoZero (γi : IdNames) : IProp GF :=
  (W64 0) ↪[γi.issued]□ (none : Option IdClaimV)

instance idNoZero_persistent (γi : IdNames) : Persistent (idNoZero (GF := GF) γi) := by
  unfold idNoZero; infer_instance

/-- **Key `k`'s claims' facts are the cluster's family at `x`** (persistent; R2c): the key's element
of the keys' facts map, a first-order parameter `x` of the family `Φs` the cluster fixes once
(`idClusterInv`), given when the key is made. The server's `x` is the incarnation's store index, so a
restarted incarnation's facts (its new store's floors) need not exist when the cluster is allocated;
being first-order, two of them agree exactly, without a later (saved predicates would add one). -/
def idKeyFactAt {X : Type} [Pos.Countable X] (fs : GName) (k : IdKey) (x : X) : IProp GF :=
  k ↪[fs]□ x

instance idKeyFactAt_persistent {X : Type} [Pos.Countable X] (fs : GName) (k : IdKey) (x : X) :
    Persistent (idKeyFactAt (GF := GF) fs k x) := by
  unfold idKeyFactAt; infer_instance

end ghostG3

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


end ghost

section ghostG1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The claimer's fact of the id `id`'s entry `v` (nothing if unclaimed): the family at its key's
parameter. -/
def idClaimFact {X : Type} [Pos.Countable X] (Φs : X → w64 → List w8 → GName → IProp GF)
    (fs : GName) (id : w64) (v : Option IdClaimV) : IProp GF :=
  match v with
  | some (d, γf, k) => iprop(∃ x : X, idKeyFactAt fs k x ∗ □ Φs x id d γf)
  | none => iprop(True)

instance idClaimFact_persistent {X : Type} [Pos.Countable X]
    (Φs : X → w64 → List w8 → GName → IProp GF) (fs : GName) (id : w64) (v : Option IdClaimV) :
    Persistent (idClaimFact (GF := GF) Φs fs id v) := by
  rcases v with _ | ⟨d, γf, k⟩ <;> unfold idClaimFact <;> infer_instance

/-- The claimers' facts over the claimed ids of the map `I`, each by its claimer's key. -/
def idClaimsFacts {X : Type} [Pos.Countable X] (Φs : X → w64 → List w8 → GName → IProp GF)
    (fs : GName) (I : GMap w64 (Option IdClaimV)) : IProp GF :=
  iprop([∗map] id ↦ v ∈ I, idClaimFact Φs fs id v)

instance idClaimsFacts_persistent {X : Type} [Pos.Countable X]
    (Φs : X → w64 → List w8 → GName → IProp GF) (fs : GName) (I : GMap w64 (Option IdClaimV)) :
    Persistent (idClaimsFacts (GF := GF) Φs fs I) := by
  unfold idClaimsFacts; infer_instance

end ghostG1

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


/-- The id's slot in the wait registry (exclusive): `Register(id)` takes it. -/
def idSlot (γi : IdNames) (id : w64) : IProp GF :=
  id ↪[γi.slot] ()

/-- **An id nobody holds** (what `Next` returns): its claim and its wait slot, and (D21e (A)) the
id of the member's prefix. -/
def idFresh (γi : IdNames) (id : w64) : IProp GF :=
  iprop(idUnclaimed γi id ∗ idSlot γi id ∗ ⌜idPfx id = γi.pfx⌝)

/-- **A `uint64` cell owned whole is no other cell's read-only one** (R2c stage 2: a new generator's
`prefix` field is no registered generator's). A fact about Perennial's points-to (through its first
byte's heap points-to, whose fractions `own 1` and `discard` do not compose), here until Perennial
has it (`notes/perennial-changes.md`). -/
theorem w64_pointsto_excl (l : Loc) (v w : w64) :
    ⊢ typedPointsto (GF := GF) l v (DFrac.own 1) -∗ typedPointsto (GF := GF) l w DFrac.discard -∗
      False := by
  iintro H1 H2
  ihave H1 := typedPointsto_split $$ H1
  ihave H2 := typedPointsto_split $$ H2
  simp only [TypedPointsto.typedPointstoDef] at *
  have h8 : ∀ n : Nat, ∃ b bs, natBytes 8 n = b :: bs := fun n => ⟨_, _, rfl⟩
  obtain ⟨b1, bs1, e1⟩ := h8 (BitVec.toNat v)
  obtain ⟨b2, bs2, e2⟩ := h8 (BitVec.toNat w)
  rw [e1, e2]
  iunfold bytesPointsto at H1 H2
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  iunfold heapPointsto at H1 H2
  icases H1 with ⟨-, H1⟩
  icases H2 with ⟨-, H2⟩
  icombine H1 H2 gives %Hv
  obtain ⟨Hv, -⟩ := Hv
  have h1 := DFrac.valid_own_op Hv
  exact absurd h1 (by simp)

/-- **A key's entry of the keys' map** (R2c stage 2): the ids its incarnation issued, and its
generator, once `NewGenerator` made it. -/
abbrev IdKeyEntry := List w64 × Option Loc

/-- **The cluster's ids** (D21e (A); by key since R2c): the issued ids' map `I` holds the reserved
`0` and exactly the ids the keys' lists `C` hold; every key's prefix good, and its ids of it; the
keys' entries, registries' cells `R` and facts `Fm` of one domain; (stage 2) one generator per key,
and a key's ids issued only once it has one. Two incarnations of one prefix are two keys: their ids are
kept apart by the issue record (`idIssueFragD`, in the prefix's `idPfxInv`), not by the prefix.
(Until T10 B6, 2026-11-26, also: distinct keys of one prefix have distinct generators, by heap
address. A restarted incarnation's heap reuses addresses, so that clause, restricted to keys of one
incarnation, became `k = (k.1, k.2)` and went; `Next` tells keys apart by the incarnation tag of the
prefix's ids' map and its generators' map, `idPfxBody`.) -/
def idClusterOk {X : Type} (I : GMap w64 (Option IdClaimV)) (C : GMap IdKey IdKeyEntry)
    (R : GMap IdKey GName) (Fm : GMap IdKey X) : Prop :=
  (∀ id, (I !! id).isSome ↔ id = W64 0 ∨ ∃ k e, C !! k = some e ∧ id ∈ e.1) ∧
  (∀ k e, C !! k = some e → idPfxOk k.1 ∧ ∀ id ∈ e.1, idPfx id = k.1) ∧
  (∀ k e, C !! k = some e → e.1 ≠ [] → e.2.isSome) ∧
  (∀ k, (C !! k).isSome ↔ (R !! k).isSome) ∧ (∀ k, (C !! k).isSome ↔ (Fm !! k).isSome)

end ghost

/-! `idClusterOk`'s clauses by name (T10, 2026-11-26): a proof outside this file reads a clause through
these, never by its position, so that adding or dropping a clause breaks only this file. -/

theorem idClusterOk.issued {X : Type} {I : GMap w64 (Option IdClaimV)} {C : GMap IdKey IdKeyEntry}
    {R : GMap IdKey GName} {Fm : GMap IdKey X} (h : idClusterOk I C R Fm) :
    ∀ id, (I !! id).isSome ↔ id = W64 0 ∨ ∃ k e, C !! k = some e ∧ id ∈ e.1 := h.1

theorem idClusterOk.pfx {X : Type} {I : GMap w64 (Option IdClaimV)} {C : GMap IdKey IdKeyEntry}
    {R : GMap IdKey GName} {Fm : GMap IdKey X} (h : idClusterOk I C R Fm) :
    ∀ k e, C !! k = some e → idPfxOk k.1 ∧ ∀ id ∈ e.1, idPfx id = k.1 := h.2.1

theorem idClusterOk.gen {X : Type} {I : GMap w64 (Option IdClaimV)} {C : GMap IdKey IdKeyEntry}
    {R : GMap IdKey GName} {Fm : GMap IdKey X} (h : idClusterOk I C R Fm) :
    ∀ k e, C !! k = some e → e.1 ≠ [] → e.2.isSome := h.2.2.1

theorem idClusterOk.domR {X : Type} {I : GMap w64 (Option IdClaimV)} {C : GMap IdKey IdKeyEntry}
    {R : GMap IdKey GName} {Fm : GMap IdKey X} (h : idClusterOk I C R Fm) :
    ∀ k, (C !! k).isSome ↔ (R !! k).isSome := h.2.2.2.1

theorem idClusterOk.domF {X : Type} {I : GMap w64 (Option IdClaimV)} {C : GMap IdKey IdKeyEntry}
    {R : GMap IdKey GName} {Fm : GMap IdKey X} (h : idClusterOk I C R Fm) :
    ∀ k, (C !! k).isSome ↔ (Fm !! k).isSome := h.2.2.2.2

/-- `idClusterOk` from its clauses by name. -/
theorem idClusterOk.mk {X : Type} {I : GMap w64 (Option IdClaimV)} {C : GMap IdKey IdKeyEntry}
    {R : GMap IdKey GName} {Fm : GMap IdKey X}
    (issued : ∀ id, (I !! id).isSome ↔ id = W64 0 ∨ ∃ k e, C !! k = some e ∧ id ∈ e.1)
    (pfx : ∀ k e, C !! k = some e → idPfxOk k.1 ∧ ∀ id ∈ e.1, idPfx id = k.1)
    (gen : ∀ k e, C !! k = some e → e.1 ≠ [] → e.2.isSome)
    (domR : ∀ k, (C !! k).isSome ↔ (R !! k).isSome)
    (domF : ∀ k, (C !! k).isSome ↔ (Fm !! k).isSome) : idClusterOk I C R Fm :=
  ⟨issued, pfx, gen, domR, domF⟩


section ghostG3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A key's generator's resources in the cluster's claims** (persistent; stage 2; heap-free since
etcd-dist D7, 2026-11-23): its prefix's ids' map's name `γip` (`gen`'s), and every id the key issued
registered there with its incarnation and its issuer. The facts the map stands for (the issue record's)
are on the prefix's member's machine, in `idPfxInv`. (Until D7: those facts themselves, here; until T10
B6, 2026-11-26, also the generator's entry of the prefix's generators' map, then named in `gen`.) -/
def idKeyGenFacts (gen : GName) (k : IdKey) (e : IdKeyEntry) : IProp GF :=
  match e.2 with
  | some g => iprop(∃ γip : GName, k.1 ↪[gen]□ γip ∗ [∗list] id ∈ e.1, id ↪[γip]□ (k.2, g))
  | none => iprop(True)

instance idKeyGenFacts_persistent (gen : GName) (k : IdKey) (e : IdKeyEntry) :
    Persistent (idKeyGenFacts (GF := GF) gen k e) := by
  unfold idKeyGenFacts; split <;> infer_instance

instance idKeyGenFacts_timeless (gen : GName) (k : IdKey) (e : IdKeyEntry) :
    Timeless (idKeyGenFacts (GF := GF) gen k e) := by
  unfold idKeyGenFacts; split <;> infer_instance

/-- (etcd-dist D7) **A prefix's names, fresh** (exclusive): the prefix's entry of `gen`, and its ids'
map, empty; `idPfxInv_alloc` makes `idPfxInv` of it on the member's machine. -/
def idPfxTok (gen : GName) (p : w64) : IProp GF :=
  iprop(∃ γip : GName, p ↪[gen]□ γip ∗ ghostMapAuth γip 1 (∅ : GMap w64 (Nat × Loc)))

/-- **The cluster's claims** (persistent; D21e (A), stage M4; by key since R2c): the issued ids'
map, the keys' entries, the registries' cells and the keys' facts, with the claimers' facts of the
claimed ids, and (stage 2) each key's generator's facts (heap-free since etcd-dist D7, at the
prefixes' names `gen`). Allocated once for the cluster (`idCluster_alloc`); every incarnation's
generator (`idGen`) and claim (`idClaim`) is over it. -/
def idClusterInv {X : Type} [Pos.Countable X] (issued cnt wn fs gen : GName)
    (Φs : X → w64 → List w8 → GName → IProp GF) : IProp GF :=
  inv idClusterN iprop(∃ (I : GMap w64 (Option IdClaimV)) (C : GMap IdKey IdKeyEntry)
      (R : GMap IdKey GName) (Fm : GMap IdKey X),
    ghostMapAuth issued 1 I ∗ ghostMapAuth cnt 1 C ∗ ghostMapAuth wn 1 R ∗ ghostMapAuth fs 1 Fm ∗
    ⌜idClusterOk I C R Fm⌝ ∗ idClaimsFacts Φs fs I ∗ [∗map] k ↦ e ∈ C, idKeyGenFacts gen k e)

instance idClusterInv_persistent {X : Type} [Pos.Countable X] (issued cnt wn fs gen : GName)
    (Φs : X → w64 → List w8 → GName → IProp GF) :
    Persistent (idClusterInv (GF := GF) issued cnt wn fs gen Φs) := by
  unfold idClusterInv; infer_instance

end ghostG3

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


/-- (etcd-dist D7) The namespace of a prefix's generators' facts. -/
def idPfxN : Namespace := nroot .@ "idutil_pfx"

@[simp] theorem idPfxN_idClusterN : (↑idPfxN : CoPset) ⊆ ⊤ \ ↑idClusterN :=
  mask_ndot_ne' nroot "idutil_pfx" "idutil_cluster" (by decide)
@[simp] theorem idPfxN_idN : (↑idPfxN : CoPset) ⊆ ⊤ \ ↑idN :=
  mask_ndot_ne' nroot "idutil_pfx" "idutil" (by decide)
@[simp] theorem idPfxN_idN_idClusterN : (↑idPfxN : CoPset) ⊆ (⊤ \ ↑idN) \ ↑idClusterN :=
  mask_ndot_ne2 nroot "idutil_pfx" "idutil" "idutil_cluster" (by decide) (by decide)

/-- (T10 B6 (b), 2026-11-26) **An id of the prefix's ids' map, with its issuer `ig = (inc, g)`**
(persistent): issued by `g`, registered as incarnation `inc`'s generator in this allocation's
generators' map `γgp`; or (after a crash) issued by an earlier incarnation. -/
def idPfxIdFact (γgp : GName) (id : w64) (ig : Nat × Loc) : IProp GF :=
  iprop((idIssueFragD id ig.2 ∗ ig.2 ↪[γgp]□ ig.1) ∨ idIssuePastD id)

instance idPfxIdFact_persistent (γgp : GName) (id : w64) (ig : Nat × Loc) :
    Persistent (idPfxIdFact (GF := GF) γgp id ig) := by
  unfold idPfxIdFact; infer_instance

instance idPfxIdFact_timeless (γgp : GName) (id : w64) (ig : Nat × Loc) :
    Timeless (idPfxIdFact (GF := GF) γgp id ig) := by
  unfold idPfxIdFact; infer_instance

/-- (etcd-dist D7) **A prefix's generators' facts**, on its member's machine: the ids issued under the
prefix, each tagged with its issuer's incarnation `i` and its issuer `g`, with the issue record's fact
that `g` issued it and `g` registered as incarnation `i`'s generator; and the generators, each with its
incarnation and its `prefix` field (its address one generator's); both maps' elements persisted.
(T10 B6 (b), 2026-11-26: the ids' map is cancelled at a crash, `idPfxInv_crash`, replaced by the old
record's authority `idIssueDeadD`; the generators' map, fresh per allocation, is never cancelled.)
(T10 B6, 2026-11-26: the incarnation tags, and the generators' map keyed to the incarnation and named
per allocation, `idPfxInv`, instead of keyed to the key and named in `gen`: within one heap a generator
is one incarnation's, and `Next` reads which from the map.) -/
def idPfxBody (γip γgp : GName) : IProp GF :=
  iprop((∃ Gp : GMap Loc Nat, ghostMapAuth γgp 1 Gp ∗
    [∗map] g ↦ i ∈ Gp,
      (∃ v : w64, structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"prefix" g ↦□ v) ∗
        g ↪[γgp]□ i) ∗
    ((∃ Ip : GMap w64 (Nat × Loc), ghostMapAuth γip 1 Ip ∗
      [∗map] id ↦ ig ∈ Ip, idPfxIdFact γgp id ig ∗ id ↪[γip]□ ig) ∨
     idIssueDeadD))

/-- (etcd-dist D7, 2026-11-23) **The prefix `p`'s generators' facts** (persistent; heap-level): its names
(`gen`'s) and the invariant of its generators' facts on the machine of the member of prefix `p`, where
its generators run and its issue record is. `NewGenerator` and `Next` open it with the cluster's
claims. (T10 B6: the generators' map's name `γgp` is the invariant's, not `gen`'s.) -/
def idPfxInv (gen : GName) (p : w64) : IProp GF :=
  iprop(∃ γip γgp : GName, p ↪[gen]□ γip ∗ inv idPfxN (idPfxBody γip γgp))

instance idPfxInv_persistent (gen : GName) (p : w64) : Persistent (idPfxInv (GF := GF) gen p) := by
  unfold idPfxInv; infer_instance

/-- (etcd-dist D7) **A prefix's facts' invariant, allocated** on its member's machine from its names. -/
theorem idPfxInv_alloc (gen : GName) (p : w64) (E : CoPset) :
    ⊢ idPfxTok (GF := GF) gen p ={E}=∗ idPfxInv gen p := by
  iintro Ht
  iunfold idPfxTok at Ht
  icases Ht with ⟨%γip, #Hp, Hi⟩
  imod (ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Nat)) with ⟨%γgp, Hg⟩
  imod (inv_alloc idPfxN E (idPfxBody (GF := GF) γip γgp)) $$ [Hi Hg] with #Hinv
  · inext
    iunfold idPfxBody
    isplitl [Hg]
    · iexists ∅
      iframe Hg
      iapply BigSepM.bigSepM_empty.2; itrivial
    · ileft
      iexists ∅
      iframe Hi
      iapply BigSepM.bigSepM_empty.2; itrivial
  imodintro
  iunfold idPfxInv
  iexists γip, γgp
  iframe Hp Hinv

/-- (etcd-dist D7) **Every prefix's facts' invariant, allocated** (one process: every member's here). -/
theorem idPfxInvs_alloc {A : Type} (gen : GName) (f : A → w64) (E : CoPset) :
    ∀ l : List A, ⊢ ([∗list] x ∈ l, idPfxTok (GF := GF) gen (f x)) ={E}=∗
      [∗list] x ∈ l, idPfxInv gen (f x)
  | [] => by
    iintro -
    imodintro
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | a :: l => by
    iintro Hs
    ihave Hs := BigSepL.bigSepL_cons.1 $$ Hs
    icases Hs with ⟨Ha, Hs⟩
    imod (idPfxInv_alloc gen (f a) E) $$ Ha with #Ha
    imod (idPfxInvs_alloc gen f E l) $$ Hs with Hs
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Ha Hs

end ghost

section ghostG2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **An incarnation's share of the cluster's ids** (D21e (A), stage M4; by key since R2c): its
key's entry of the keys' map, no id issued and no generator yet, its wait slots' map and (stage 2)
its pending ids' map, empty. `NewGenerator` takes it. -/
def idShare (γi : IdNames) : IProp GF :=
  iprop(γi.key ↪[γi.cnt] ((([] : List w64), (none : Option Loc)) : IdKeyEntry) ∗
    ghostMapAuth γi.slot 1 (∅ : GMap w64 Unit) ∗ ghostMapAuth γi.pend 1 (∅ : GMap w64 Unit))

end ghostG2

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


/-- **The generator `g`** (persistent): its `prefix` field fixed at the member's prefix `γi.pfx`
(its 48 low bits 0: the member id shifted by 48, so ids of distinct suffixes differ), its `suffix`
(a plain `uint64` field the code updates with `atomic.AddUint64`) in an invariant with the count `k`
of `Next`'s increments, backed by `k` time receipts (D19b), its key's entry of the cluster's keys'
map (the ids issued `L`, and `g` itself) and its wait slots' map; and the cluster's claims, its key's
facts `Φ` the cluster's family at the key's parameter (R2c). (Stage 2: `Next` counts an id at its
increment and issues it at its issue step, `idutil`'s trusted model; between the two the id is
pending, `P`: the counted ids, `idIssued`, are the issued and the pending ones, disjoint, and all have
wait slots.) And its prefix's generators' facts (`idPfxInv`'s, opened: T10 B6, 2026-11-26), with `g`
registered there as the incarnation's generator. `NewGenerator` establishes it; `Next`, under the
receipts' bound (`idCred`), returns an `idFresh` id. -/
def idGen (γi : IdNames) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) : IProp GF :=
  iprop(∃ s0 : w64, ⌜g ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"prefix" g ↦□ γi.pfx ∗
    ⌜uint.Z s0 < 2 ^ 48 ∧ γi.pfx &&& W64 (2 ^ 48 - 1) = W64 0⌝ ∗
    inv idN iprop(∃ (k : Nat) (L : List w64) (S P : GMap w64 Unit),
      structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"suffix" g ↦
        (s0 + W64 (k : Int)) ∗
      ⧗ k ∗
      γi.key ↪[γi.cnt] ((L, some g) : IdKeyEntry) ∗ ghostMapAuth γi.slot 1 S ∗
      ghostMapAuth γi.pend 1 P ∗
      ⌜∀ id, ((id ∈ L ∨ (P !! id).isSome) ↔ idIssued γi.pfx s0 k id) ∧
        ((S !! id).isSome ↔ idIssued γi.pfx s0 k id) ∧ (id ∈ L → P !! id = none)⌝) ∗
    ∃ (X : Type) (_ : Pos.Countable X) (Φs : X → w64 → List w8 → GName → IProp GF) (x : X),
      ⌜Φs x = Φ⌝ ∗ idKeyFactAt γi.fs γi.key x ∗ idClusterInv γi.issued γi.cnt γi.wn γi.fs γi.gen Φs ∗
      ∃ γip γgp : GName, γi.pfx ↪[γi.gen]□ γip ∗ inv idPfxN (idPfxBody γip γgp) ∗ g ↪[γgp]□ γi.inc)

instance idGen_persistent (γi : IdNames) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) :
    Persistent (idGen (GF := GF) γi g Φ) := by
  unfold idGen; infer_instance

end ghost

section ghostG1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A key's entry of the registries' map, not yet set** (exclusive; linkv-txn stage B1,
2026-10-20; by key since R2c): the map's (persistent) element of the key names a cell the
incarnation owns, empty; its `start` sets it to its wait registry's ghost name (`idWaitTok_set`). -/
def idWaitTokAt (wn : GName) (k : IdKey) : IProp GF :=
  iprop(∃ γp : GName, k ↪[wn]□ γp ∗ dghostVar γp (DFrac.own 1) (none : Option GName))

/-- `idWaitTokAt` at the incarnation's names. -/
abbrev idWaitTok (γi : IdNames) : IProp GF := idWaitTokAt γi.wn γi.key

end ghostG1

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


end ghost

section ghostG1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The incarnation of key `k` registers its requests in the wait registry `W`** (persistent;
linkv-txn stage B1; by key since R2c): the cell of `k`'s element of the registries' map, set to
`W`. -/
def idWaitIs (γi : IdNames) (k : IdKey) (W : GName) : IProp GF :=
  iprop(∃ γp : GName, k ↪[γi.wn]□ γp ∗ dghostVar γp DFrac.discard (some W))

instance idWaitIs_persistent (γi : IdNames) (k : IdKey) (W : GName) :
    Persistent (idWaitIs (GF := GF) γi k W) := by
  unfold idWaitIs; infer_instance

end ghostG1

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


/-- A key's registry is unique. -/
theorem idWaitIs_agree (γi : IdNames) (k : IdKey) (W W' : GName) :
    ⊢ idWaitIs (GF := GF) γi k W -∗ idWaitIs γi k W' -∗ ⌜W = W'⌝ := by
  unfold idWaitIs
  iintro ⟨%γp, #H1, #C1⟩ ⟨%γp', #H2, #C2⟩
  ihave %Hp := ghostMapElem_agree $$ H1 H2
  subst Hp
  ihave %Hw := dghostVar_agree γp (some W) DFrac.discard (some W') DFrac.discard $$ C1 C2
  ipureintro
  exact Option.some.inj Hw

/-- Setting an incarnation's entry of the registries' map. -/
theorem idWaitTok_set (γi : IdNames) (W : GName) :
    ⊢ idWaitTok (GF := GF) γi ==∗ idWaitIs γi γi.key W := by
  unfold idWaitTok idWaitTokAt idWaitIs
  iintro ⟨%γp, #Hp, Hc⟩
  imod dghostVar_update (some W) γp (none : Option GName) $$ Hc with Hc
  imod dghostVar_persist γp 1 (some W) $$ Hc with #Hc
  imodintro
  iexists γp
  iframe Hp Hc

end ghost

section ghostG2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A new key** (R2c): into maps without it, the key's empty entry (no id, no generator), its
unset registry cell and its facts' parameter `x`. -/
theorem idKey_insert {X : Type} [Pos.Countable X] (cnt wn fs : GName) (C : GMap IdKey IdKeyEntry)
    (R : GMap IdKey GName) (Fm : GMap IdKey X) (k : IdKey) (x : X)
    (hC : C !! k = none) (hR : R !! k = none) (hF : Fm !! k = none) :
    ⊢ ghostMapAuth (GF := GF) cnt 1 C -∗ ghostMapAuth wn 1 R -∗ ghostMapAuth fs 1 Fm ==∗
      ∃ γp : GName,
        ghostMapAuth cnt 1 (C.insert k (([], none) : IdKeyEntry)) ∗ ghostMapAuth wn 1 (R.insert k γp) ∗
        ghostMapAuth fs 1 (Fm.insert k x) ∗
        k ↪[cnt] ((([] : List w64), (none : Option Loc)) : IdKeyEntry) ∗ idWaitTokAt wn k ∗
        idKeyFactAt fs k x := by
  iintro HC HR HF
  imod ghost_map_insert k ((([] : List w64), (none : Option Loc)) : IdKeyEntry) hC $$ HC with ⟨HC, Hk⟩
  imod dghostVar_alloc (GF := GF) (none : Option GName) with ⟨%γp, Hc⟩
  imod ghost_map_insert_persist k γp hR $$ HR with ⟨HR, #Hp⟩
  imod ghost_map_insert_persist k x hF $$ HF with ⟨HF, #Hxk⟩
  imodintro
  iexists γp
  iframe HC HR HF Hk
  isplitl
  · iunfold idWaitTokAt; iexists γp; iframe Hp Hc
  · iunfold idKeyFactAt; iexact Hxk

/-- (etcd-dist D7) **Each prefix's names, allocated** (`idCluster_alloc`'s): for distinct prefixes not
yet in `gen`'s map, each's `idPfxTok`. -/
theorem idPfxToks_alloc (gen : GName) (ps : List w64) (Gn : GMap w64 GName)
    (Hnd : ps.Nodup) (Hfr : ∀ p ∈ ps, Gn !! p = none) :
    ⊢ ghostMapAuth (GF := GF) gen 1 Gn ==∗ ∃ Gn' : GMap w64 GName,
      ghostMapAuth gen 1 Gn' ∗ [∗list] p ∈ ps, idPfxTok gen p := by
  induction ps generalizing Gn with
  | nil =>
    iintro H
    imodintro
    iexists Gn
    iframe H
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  | cons q qs ih =>
    iintro H
    have hnd := List.nodup_cons.1 Hnd
    imod (ghost_map_alloc_empty (GF := GF) (K := w64) (V := Nat × Loc)) with ⟨%γip, Hi⟩
    imod (ghost_map_insert_persist q γip (Hfr q (List.mem_cons_self ..))) $$ H with ⟨H, #Hq⟩
    imod (ih (Gn.insert q γip) hnd.2 (fun p hp => by
        rw [GMap.lookup_insert_ne _ _ (fun h => hnd.1 (by subst h; exact hp))]
        exact Hfr p (List.mem_cons_of_mem _ hp))) $$ H with ⟨%Gn', H, Hqs⟩
    imodintro
    iexists Gn'
    iframe H
    iapply BigSepL.bigSepL_cons.2
    iframe Hqs
    iunfold idPfxTok
    iexists γip
    iframe Hq Hi

/-- **The cluster's claims, allocated** (D21e (A), stage M4; by key since R2c) for the members'
prefixes `ps`, under the pure premise that they are good and distinct
(`nonissues/etcd-request-id-member-prefix.md`): the claims invariant at the facts' family `Φs` (the
caller's choice), the reserved id `0` (`idNoZero`, D19c) and each member's first incarnation's key
`(p, 0)` -- its entry of the keys' map, empty (with its slots and pending map, the caller's,
`idShare`), its unset registry cell and its facts' parameter `xs p` (the caller's choice); (etcd-dist D7)
and each prefix's names (`idPfxTok`), from which its member's machine makes its `idPfxInv`. -/
theorem idCluster_alloc {X : Type} [Pos.Countable X] (ps : List w64)
    (Φs : X → w64 → List w8 → GName → IProp GF) (xs : w64 → X)
    (E : CoPset) (Hnd : ps.Nodup) (Hok : ∀ p ∈ ps, idPfxOk p) :
    ⊢ |={E}=> ∃ issued cnt wn fs gen : GName, idClusterInv (GF := GF) issued cnt wn fs gen Φs ∗
      (W64 0) ↪[issued]□ (none : Option IdClaimV) ∗
      ([∗list] p ∈ ps, (p, 0) ↪[cnt] ((([] : List w64), (none : Option Loc)) : IdKeyEntry) ∗
        idWaitTokAt wn (p, 0) ∗ idKeyFactAt fs (p, 0) (xs p)) ∗
      [∗list] p ∈ ps, idPfxTok gen p := by
  istart
  imod (ghost_map_alloc_empty (K := w64) (V := GName)) with ⟨%γG, HG0⟩
  imod (idPfxToks_alloc (GF := GF) γG ps ∅ Hnd (fun p _ => GMap.lookup_empty _)) $$ HG0
    with ⟨%Gn, -, Htoks⟩
  imod (ghost_map_alloc_empty (K := w64) (V := Option IdClaimV)) with ⟨%γI, HI⟩
  imod (ghost_map_alloc_empty (K := IdKey) (V := IdKeyEntry)) with ⟨%γC, HC⟩
  imod (ghost_map_alloc_empty (K := IdKey) (V := GName)) with ⟨%γR, HR⟩
  imod (ghost_map_alloc_empty (K := IdKey) (V := X)) with ⟨%γF, HF⟩
  imod ghost_map_insert_persist (W64 0) (none : Option IdClaimV) (GMap.lookup_empty _)
    $$ HI with ⟨HI, #H0⟩
  -- each prefix's first key, inserted into the three maps, which keep one domain: the keys of
  -- the prefixes inserted so far, each empty
  have hgen : ∀ (qs : List w64) (C : GMap IdKey IdKeyEntry) (R : GMap IdKey GName)
      (Fm : GMap IdKey X),
      qs.Nodup → (∀ q ∈ qs, idPfxOk q) →
      (∀ k, (C !! k).isSome ↔ (R !! k).isSome) → (∀ k, (C !! k).isSome ↔ (Fm !! k).isSome) →
      (∀ k e, C !! k = some e → idPfxOk k.1 ∧ e = ([], none) ∧ k.2 = 0 ∧ k.1 ∉ qs) →
      ⊢ ghostMapAuth (GF := GF) γC 1 C -∗ ghostMapAuth γR 1 R -∗ ghostMapAuth γF 1 Fm ==∗
        ∃ (C' : GMap IdKey IdKeyEntry) (R' : GMap IdKey GName) (Fm' : GMap IdKey X),
          ghostMapAuth γC 1 C' ∗ ghostMapAuth γR 1 R' ∗ ghostMapAuth γF 1 Fm' ∗
          ⌜(∀ k, (C' !! k).isSome ↔ (R' !! k).isSome) ∧ (∀ k, (C' !! k).isSome ↔ (Fm' !! k).isSome) ∧
            (∀ k e, C' !! k = some e → idPfxOk k.1 ∧ e = ([], none))⌝ ∗
          [∗list] p ∈ qs, (p, 0) ↪[γC] ((([] : List w64), (none : Option Loc)) : IdKeyEntry) ∗
            idWaitTokAt γR (p, 0) ∗ idKeyFactAt γF (p, 0) (xs p) := by
    intro qs
    induction qs with
    | nil =>
      intro C R Fm _ _ hR hF hC
      iintro HC HR HF
      imodintro
      iexists C, R, Fm
      iframe HC HR HF
      isplitr
      · ipureintro
        exact ⟨hR, hF, fun k e h => ⟨(hC k e h).1, (hC k e h).2.1⟩⟩
      iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      itrivial
    | cons q qs ih =>
      intro C R Fm hnd hok hR hF hC
      have hnd' := List.nodup_cons.1 hnd
      have hq0 : C !! (q, 0) = none := by
        cases h : C !! (q, 0) with
        | none => rfl
        | some e => exact absurd (List.mem_cons_self ..) (hC _ e h).2.2.2
      have hqR : R !! (q, 0) = none := by
        cases h : R !! (q, 0) with
        | none => rfl
        | some _ => have := (hR (q, 0)).2 (by simp [h]); simp [hq0] at this
      have hqF : Fm !! (q, 0) = none := by
        cases h : Fm !! (q, 0) with
        | none => rfl
        | some _ => have := (hF (q, 0)).2 (by simp [h]); simp [hq0] at this
      iintro HC HR HF
      imod (idKey_insert γC γR γF C R Fm (q, 0) (xs q) hq0 hqR hqF) $$ HC HR HF
        with ⟨%γp, HC, HR, HF, Hk, Hw, Hf⟩
      imod (ih (C.insert (q, 0) ([], none)) (R.insert (q, 0) γp) (Fm.insert (q, 0) (xs q)) hnd'.2
          (fun r hr => hok r (List.mem_cons_of_mem _ hr))
          (fun k => by
            rw [GMap.lookup_insert_is_Some, GMap.lookup_insert_is_Some, hR k])
          (fun k => by
            rw [GMap.lookup_insert_is_Some, GMap.lookup_insert_is_Some, hF k])
          (fun k e h => by
            rw [GMap.lookup_insert_eq_iff] at h
            by_cases hk : (q, 0) = k
            · subst hk
              simp at h
              exact ⟨hok q (List.mem_cons_self ..), h.symm, rfl, hnd'.1⟩
            · simp only [hk, ite_false] at h
              obtain ⟨h1, h2, h3, h4⟩ := hC k e h
              exact ⟨h1, h2, h3, fun hm => h4 (List.mem_cons_of_mem _ hm)⟩)) $$ HC HR HF
        with ⟨%C', %R', %Fm', HC, HR, HF, %Hok', Hqs⟩
      imodintro
      iexists C', R', Fm'
      iframe HC HR HF
      isplitr
      · ipureintro; exact Hok'
      iapply BigSepL.bigSepL_cons.2
      iframe Hk Hw Hf Hqs
  imod (hgen ps ∅ ∅ ∅ Hnd Hok (fun k => by simp [GMap.lookup_empty])
      (fun k => by simp [GMap.lookup_empty]) (fun k e h => by simp [GMap.lookup_empty] at h)) $$ HC HR HF
    with ⟨%C, %R, %Fm, HC, HR, HF, %HCok, Hps⟩
  obtain ⟨hR, hF, hCe⟩ := HCok
  have hG : (emp : IProp GF) ⊢ [∗map] k ↦ e ∈ C, idKeyGenFacts (GF := GF) γG k e :=
    BigSepM.bigSepM_intro (fun {k e} hke => by
      rw [(hCe k e hke).2]; unfold idKeyGenFacts; exact true_intro)
  ihave #HG : iprop([∗map] k ↦ e ∈ C, idKeyGenFacts (GF := GF) γG k e) $$ []
  · iapply hG; iempintro
  imod (inv_alloc idClusterN E iprop(∃ (I : GMap w64 (Option IdClaimV)) (C : GMap IdKey IdKeyEntry)
      (R : GMap IdKey GName) (Fm : GMap IdKey X),
      ghostMapAuth γI 1 I ∗ ghostMapAuth γC 1 C ∗ ghostMapAuth γR 1 R ∗ ghostMapAuth γF 1 Fm ∗
      ⌜idClusterOk I C R Fm⌝ ∗ idClaimsFacts Φs γF I ∗ [∗map] k ↦ e ∈ C, idKeyGenFacts γG k e))
    $$ [HI HC HR HF] with #Hinv
  · inext
    iexists ((∅ : GMap w64 (Option IdClaimV)).insert (W64 0) none), C, R, Fm
    iframe HI HC HR HF HG
    isplitr
    · ipureintro
      refine ⟨?_, ?_, ?_, hR, hF⟩
      · intro id
        rw [GMap.lookup_insert_is_Some, GMap.lookup_empty]
        constructor
        · rintro (h | ⟨-, h⟩)
          · exact Or.inl h.symm
          · simp at h
        · rintro (h | ⟨k, e, hke, hid⟩)
          · exact Or.inl h.symm
          · rw [(hCe k e hke).2] at hid; simp at hid
      · intro k e hke
        refine ⟨(hCe k e hke).1, ?_⟩
        rw [(hCe k e hke).2]; simp
      · intro k e hke hne
        rw [(hCe k e hke).2] at hne; exact absurd rfl hne
    iunfold idClaimsFacts
    iapply (BigSepM.bigSepM_insert (PROP := IProp GF)
      (m := (∅ : GMap w64 (Option IdClaimV)))
      (Φ := fun id v => idClaimFact Φs γF id v) (GMap.lookup_empty _)).2
    isplitr
    · iunfold idClaimFact; itrivial
    iapply BigSepM.bigSepM_empty.2
    itrivial
  imodintro
  iexists γI, γC, γR, γF, γG
  iframe H0 Hps Htoks
  iunfold idClusterInv
  iexact Hinv

end ghostG2

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


/-- An incarnation number above every key's of a finite map. -/
theorem idKey_fresh_inc {V : Type} (C : GMap IdKey V) : ∃ n : Nat, ∀ k v, C !! k = some v → k.2 < n := by
  have hmax : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro x hx; simp at hx
    | cons a l ih =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp only [List.foldr_cons]; omega
      · have := ih x hx; simp only [List.foldr_cons]; omega
  refine ⟨(C.toList.map (fun kv : IdKey × V => kv.1.2)).foldr max 0 + 1, fun k v h => ?_⟩
  have hm := (GMap.mem_toList C k v).2 h
  have hmem : k.2 ∈ C.toList.map (fun kv : IdKey × V => kv.1.2) :=
    List.mem_map.2 ⟨(k, v), hm, rfl⟩
  have := hmax _ k.2 hmem
  omega

end ghost

section ghostG1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A new incarnation's key** (the restart plan's R2c stage 2: a member's restart): for the good
prefix `p`, a key `(p, inc)` no key of the cluster has, with its empty entry, its unset registry cell
and its facts' parameter `x`. The number is chosen above every key's: nothing is handed from one
incarnation to the next. -/
theorem idIncarnation_alloc {X : Type} [Pos.Countable X] (issued cnt wn fs gen : GName)
    (Φs : X → w64 → List w8 → GName → IProp GF) (p : w64) (x : X) (E : CoPset)
    (HE : ↑idClusterN ⊆ E) (Hp : idPfxOk p) :
    ⊢ idClusterInv (GF := GF) issued cnt wn fs gen Φs ={E}=∗ ∃ inc : Nat,
      (p, inc) ↪[cnt] ((([] : List w64), (none : Option Loc)) : IdKeyEntry) ∗
      idWaitTokAt wn (p, inc) ∗ idKeyFactAt fs (p, inc) x := by
  iintro #Hcl
  iunfold idClusterInv at Hcl
  iinv Hcl with Hi Hclose
  icases Hi with ⟨%I, %C, %R, %Fm, >HI, >HC, >HR, >HF, >%Hok, #HFs, >#HG⟩
  obtain ⟨n, hn⟩ := idKey_fresh_inc C
  have hC : C !! (p, n) = none := by
    cases h : C !! (p, n) with
    | none => rfl
    | some v => exact absurd (hn _ v h) (Nat.lt_irrefl n)
  have hR : R !! (p, n) = none := by
    cases h : R !! (p, n) with
    | none => rfl
    | some _ => have := (Hok.domR (p, n)).2 (by simp [h]); simp [hC] at this
  have hF : Fm !! (p, n) = none := by
    cases h : Fm !! (p, n) with
    | none => rfl
    | some _ => have := (Hok.domF (p, n)).2 (by simp [h]); simp [hC] at this
  imod (idKey_insert cnt wn fs C R Fm (p, n) x hC hR hF) $$ HC HR HF
    with ⟨%γp, HC, HR, HF, Hk, Hw, Hf⟩
  imod Hclose $$ [HI HC HR HF] with -
  · inext
    iexists I, (C.insert (p, n) ([], none)), (R.insert (p, n) γp), (Fm.insert (p, n) x)
    iframe HI HC HR HF HFs
    obtain ⟨h1, h2, h4, h5, h6⟩ := Hok
    isplitr
    · ipureintro
      refine ⟨fun id => ?_, fun k e hke => ?_, fun k e hke hne => ?_, fun k => ?_, fun k => ?_⟩
      · rw [h1 id]
        apply or_congr Iff.rfl
        constructor
        · rintro ⟨k, e, hke, hid⟩
          exact ⟨k, e, by
            rw [GMap.lookup_insert_ne _ _ (fun h => by subst h; rw [hC] at hke; cases hke)]
            exact hke, hid⟩
        · rintro ⟨k, e, hke, hid⟩
          by_cases hk : (p, n) = k
          · subst hk; rw [GMap.lookup_insert] at hke; cases hke; simp at hid
          · exact ⟨k, e, by rw [GMap.lookup_insert_ne _ _ hk] at hke; exact hke, hid⟩
      · by_cases hk : (p, n) = k
        · subst hk; rw [GMap.lookup_insert] at hke; cases hke; exact ⟨Hp, by simp⟩
        · rw [GMap.lookup_insert_ne _ _ hk] at hke; exact h2 k e hke
      · by_cases hk : (p, n) = k
        · subst hk; rw [GMap.lookup_insert] at hke; cases hke; exact absurd rfl hne
        · rw [GMap.lookup_insert_ne _ _ hk] at hke; exact h4 k e hke hne
      · rw [GMap.lookup_insert_is_Some, GMap.lookup_insert_is_Some, h5 k]
      · rw [GMap.lookup_insert_is_Some, GMap.lookup_insert_is_Some, h6 k]
    iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (m := C)
      (Φ := fun k e => idKeyGenFacts (GF := GF) gen k e) hC).2
    iframe HG
    iunfold idKeyGenFacts
    itrivial
  imodintro
  iexists n
  iframe Hk Hw Hf

end ghostG1

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]


end ghost

end EtcdGrove
end Perennial
