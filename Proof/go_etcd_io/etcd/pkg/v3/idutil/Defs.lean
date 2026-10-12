/-
`pkg/idutil` (the request id generator): the shared vocabulary of its specs (`NewGenerator`,
`Generator.Next`), used by the server's request path (`etcdserver/InvRequest.lean`) and the wait
registry (`wait/Defs.lean`: an id's wait slot). Lean-first (no Rocq counterpart); moved here from
the server's `InvRequest.lean` (unit 0 of the request path) in unit 2 (2026-10-12).

**Unique ids** (`idGen`, `idFresh`, `idClaim`): `Generator.Next` returns `prefix |
lowbit(suffix, 48)` for an atomically incremented `suffix`: `2 ^ 48` consecutive calls return
distinct ids. `idGen γi g` hands out `2 ^ 48 - 1` credits (`idCred`), `Next` consumes one and
returns an id nobody holds (`idFresh γi id`: the right to claim the id for a request's data,
`idClaim γi id d` (persistent, agreeing), and the id's slot in the wait registry, `idSlot`).
The ids of other members' requests (other generators, other prefixes) are claimed in the same
map: that the members' prefixes (`uint16(memberID)`) differ is a premise of the raft contract's
apply side (`issues/etcd-request-id-member-prefix.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Perennial.Ghost.GhostMap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- The id generator's ghost names: the credits (`Auth Nat`), and two ghost maps keyed by id:
the data an id was claimed for (`none` until claimed), and the id's wait slot. -/
structure IdNames where
  cred : GName
  issued : GName
  slot : GName

/-- `id` is among the first `k` ids of the generator with prefix `pfx` and initial suffix
`s0`: `pfx | lowbit(s0 + j, 48)` for `1 ≤ j ≤ k`. -/
def idIssued (pfx s0 : w64) (k : Nat) (id : w64) : Prop :=
  ∃ j : Nat, 1 ≤ j ∧ j ≤ k ∧ id = pfx ||| ((s0 + W64 (j : Int)) &&& W64 (2 ^ 48 - 1))

def idN : Namespace := nroot .@ "idutil"

section ghost
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `n` id credits (one per `Next`). -/
def idCred (γi : IdNames) (n : Nat) : IProp GF := own γi.cred (◯ n : Auth Nat)

/-- The right to claim the id `id` for a request's data. -/
def idUnclaimed (γi : IdNames) (id : w64) : IProp GF :=
  id ↪[γi.issued] (none : Option (List w8))

/-- The id `id` was claimed for the data `d` (persistent; agreeing). -/
def idClaim (γi : IdNames) (id : w64) (d : List w8) : IProp GF :=
  id ↪[γi.issued]□ (some d)

instance idClaim_persistent (γi : IdNames) (id : w64) (d : List w8) :
    Persistent (idClaim (GF := GF) γi id d) := by
  unfold idClaim; infer_instance

/-- The id's slot in the wait registry (exclusive): `Register(id)` takes it. -/
def idSlot (γi : IdNames) (id : w64) : IProp GF :=
  id ↪[γi.slot] ()

/-- **An id nobody holds** (what `Next` returns): its claim and its wait slot. -/
def idFresh (γi : IdNames) (id : w64) : IProp GF :=
  iprop(idUnclaimed γi id ∗ idSlot γi id)

/-- **The generator `g`** (persistent): its `prefix` field fixed (its 48 low bits 0: the
member id shifted by 48, so ids of distinct suffixes differ), its `suffix` (a plain `uint64` field
the code updates with `atomic.AddUint64`) in an
invariant with the credits' authority (`2 ^ 48 - 1` less the `k` ids issued) and the issued
ids' ghost maps (the ids issued, `idIssued`, and only those, are in both maps). `NewGenerator`
establishes it with `idCred γi (2 ^ 48 - 1)`; `Next` consumes a credit and returns an
`idFresh` id. The bound is the premise that a process issues fewer than `2 ^ 48` request ids
(the 48-bit suffix wraps after `2 ^ 48`). -/
def idGen (γi : IdNames) (g : Loc) : IProp GF :=
  iprop(∃ (pfx s0 : w64), ⌜g ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"prefix" g ↦□ pfx ∗
    ⌜uint.Z s0 < 2 ^ 48 ∧ pfx &&& W64 (2 ^ 48 - 1) = W64 0⌝ ∗
    inv idN iprop(∃ (k : Nat) (I : GMap w64 (Option (List w8))) (S : GMap w64 Unit),
      structFieldRef go_etcd_io.etcd.pkg.v3.idutil.Generator go!"suffix" g ↦
        (s0 + W64 (k : Int)) ∗
      own γi.cred (● (2 ^ 48 - 1 - k) : Auth Nat) ∗ ⌜k ≤ 2 ^ 48 - 1⌝ ∗
      ghostMapAuth γi.issued 1 I ∗ ghostMapAuth γi.slot 1 S ∗
      ⌜∀ id, ((I !! id).isSome ↔ idIssued pfx s0 k id) ∧ ((S !! id).isSome ↔ idIssued pfx s0 k id)⌝))

instance idGen_persistent (γi : IdNames) (g : Loc) : Persistent (idGen (GF := GF) γi g) := by
  unfold idGen; infer_instance

end ghost

end EtcdGrove
end Perennial
