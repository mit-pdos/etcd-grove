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

The ids of other members' requests (other generators, other prefixes) are claimed in the same
map: that the members' prefixes (`uint16(memberID)`) differ is a premise of the raft contract's
apply side (`issues/etcd-request-id-member-prefix.md`).

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
public import Perennial.GooseLang.Receipts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- The id generator's ghost names: two ghost maps keyed by id: the data an id was claimed for
(`none` until claimed), and the id's wait slot. (Until D19b, 2026-10-18, also the issued ids'
counter, `cred`: a monotone counter from D17, the credits' `Auth Nat` before; the time receipts
in the invariant count the ids now.) -/
structure IdNames where
  issued : GName
  slot : GName

/-- `id` is among the first `k` ids of the generator with prefix `pfx` and initial suffix
`s0`: `pfx | lowbit(s0 + j, 48)` for `1 ≤ j ≤ k`. -/
def idIssued (pfx s0 : w64) (k : Nat) (id : w64) : Prop :=
  ∃ j : Nat, 1 ≤ j ∧ j ≤ k ∧ id = pfx ||| ((s0 + W64 (j : Int)) &&& W64 (2 ^ 48 - 1))

/-- **The id `0` is reserved** in a generator of prefix `pfx` that is not `0` (D19c,
2026-10-18): such a generator never issues `0` (`idutil_or_ne_zero`), and its issued ids' map
holds `0 ↦ none`, read-only (`idNoZero`), so that no request claims `0`, the id of raft's
bootstrap conf changes (`issues/etcd-request-id-zero-bootstrap-confchange.md`: a generator of
prefix `0` does issue it). -/
def idReserved (pfx id : w64) : Prop := id = W64 0 ∧ pfx ≠ W64 0

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

def idN : Namespace := nroot .@ "idutil"

/-- The `n` low bits of `x`, as a number. -/
theorem idutil_mask_toNat (x : BitVec 64) (n : Nat) (h : n ≤ 64) :
    (x &&& BitVec.ofNat 64 (2 ^ n - 1)).toNat = x.toNat % 2 ^ n := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have h1 : 2 ^ n - 1 < 2 ^ 64 := by
    have : 2 ^ n ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) h
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [Nat.mod_eq_of_lt h1, Nat.and_two_pow_sub_one_eq_mod]

section ghost
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

/-- The right to claim the id `id` for a request's data. -/
def idUnclaimed (γi : IdNames) (id : w64) : IProp GF :=
  id ↪[γi.issued] (none : Option (List w8 × GName))

/-- The id `id` was claimed for the data `d`, with the claimer's ghost name `γf` (persistent;
agreeing). -/
def idClaim (γi : IdNames) (id : w64) (d : List w8) (γf : GName) : IProp GF :=
  id ↪[γi.issued]□ (some (d, γf))

instance idClaim_persistent (γi : IdNames) (id : w64) (d : List w8) (γf : GName) :
    Persistent (idClaim (GF := GF) γi id d γf) := by
  unfold idClaim; infer_instance

/-- **No request claims the id `0`** (persistent; D19c): the issued ids' map holds `0 ↦ none`,
read-only. `NewGenerator` gives it for a member id whose 16 low bits are not `0`
(`idReserved`). -/
def idNoZero (γi : IdNames) : IProp GF :=
  (W64 0) ↪[γi.issued]□ (none : Option (List w8 × GName))

instance idNoZero_persistent (γi : IdNames) : Persistent (idNoZero (GF := GF) γi) := by
  unfold idNoZero; infer_instance

/-- The claimer's fact of the id `id`'s entry `v` (nothing if unclaimed). -/
def idClaimFact (Φ : w64 → List w8 → GName → IProp GF) (id : w64)
    (v : Option (List w8 × GName)) : IProp GF :=
  match v with
  | some (d, γf) => iprop(□ Φ id d γf)
  | none => iprop(True)

/-- The claimers' facts over the claimed ids of the map `I`. -/
def idClaimsFacts (Φ : w64 → List w8 → GName → IProp GF)
    (I : GMap w64 (Option (List w8 × GName))) : IProp GF :=
  iprop([∗map] id ↦ v ∈ I, idClaimFact Φ id v)

/-- The id's slot in the wait registry (exclusive): `Register(id)` takes it. -/
def idSlot (γi : IdNames) (id : w64) : IProp GF :=
  id ↪[γi.slot] ()

/-- **An id nobody holds** (what `Next` returns): its claim and its wait slot. -/
def idFresh (γi : IdNames) (id : w64) : IProp GF :=
  iprop(idUnclaimed γi id ∗ idSlot γi id)

/-- **The generator `g`** (persistent): its `prefix` field fixed (its 48 low bits 0: the
member id shifted by 48, so ids of distinct suffixes differ), its `suffix` (a plain `uint64` field
the code updates with `atomic.AddUint64`) in an
invariant with the issued ids' count `k`, backed by `k` time receipts (D19b; from D17 a
monotone counter, before it the credits' authority, `2 ^ 48 - 1` less `k`) and the issued ids' ghost maps (the ids issued, `idIssued`, and only those, are in both maps; since D19c the issued map also holds the reserved id `0` of a prefix not `0`, `idReserved`), and the
claimers' facts `Φ` of the claimed ones (unit V2). `NewGenerator`
establishes it; `Next`, under the receipts' bound (`idCred`), counts one more id and returns an
`idFresh` id. -/
def idGen (γi : IdNames) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) : IProp GF :=
  iprop(∃ (pfx s0 : w64), ⌜g ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"prefix" g ↦□ pfx ∗
    ⌜uint.Z s0 < 2 ^ 48 ∧ pfx &&& W64 (2 ^ 48 - 1) = W64 0⌝ ∗
    inv idN iprop(∃ (k : Nat) (I : GMap w64 (Option (List w8 × GName))) (S : GMap w64 Unit),
      structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"suffix" g ↦
        (s0 + W64 (k : Int)) ∗
      ⧗ k ∗
      ghostMapAuth γi.issued 1 I ∗ ghostMapAuth γi.slot 1 S ∗
      ⌜∀ id, ((I !! id).isSome ↔ idIssued pfx s0 k id ∨ idReserved pfx id) ∧
        ((S !! id).isSome ↔ idIssued pfx s0 k id)⌝ ∗
      idClaimsFacts Φ I))

instance idGen_persistent (γi : IdNames) (g : Loc) (Φ : w64 → List w8 → GName → IProp GF) :
    Persistent (idGen (GF := GF) γi g Φ) := by
  unfold idGen; infer_instance

/-- **Fresh generator names** (2026-10-16, D13a: the names chosen before the call): the two
empty ghost maps (until D19b also the issued ids' counter at `0`). `NewGenerator` takes them,
so that its caller knows the names before the call (`idNamesFresh_alloc`). -/
def idNamesFresh (γi : IdNames) : IProp GF :=
  iprop(ghostMapAuth γi.issued 1 (∅ : GMap w64 (Option (List w8 × GName))) ∗
    ghostMapAuth γi.slot 1 (∅ : GMap w64 Unit))

/-- Fresh generator names are allocated. -/
theorem idNamesFresh_alloc : ⊢ |==> ∃ γi : IdNames, idNamesFresh (GF := GF) γi := by
  istart
  imod (ghost_map_alloc_empty (K := w64) (V := Option (List w8 × GName))) with ⟨%γI, HI⟩
  imod (ghost_map_alloc_empty (K := w64) (V := Unit)) with ⟨%γS, HS⟩
  imodintro
  iexists ⟨γI, γS⟩
  iunfold idNamesFresh
  iframe HI HS

end ghost

end EtcdGrove
end Perennial
