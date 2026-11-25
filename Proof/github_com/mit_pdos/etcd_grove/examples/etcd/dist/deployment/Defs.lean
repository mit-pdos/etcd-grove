/- Lean-first (no Rocq counterpart).

# `etcd/dist/deployment`: the vocabulary of its functions' specs

What Go's `deployment` functions compute, over the Go-mirror values of `TopLevelDefs.lean` (kinds as
`w64`, parameters as Go `int`s): the kinds' predicates, `NodeCount`, `boundsOk`, `compatible`, the
member ids' check. `DeploymentDefs.lean` gives the typed meaning; the bridge lemmas from these to it
are in `WellFormedLemmas.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Repr
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentDefs
public import Perennial.TrustedCode.crypto.fips140

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

/-- A byte `nameOk` admits (an ASCII letter or digit, or `-`). -/
def nameByteOk (b : w8) : Bool := decide
  ((48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨ (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨
    (97 ≤ b.toNat ∧ b.toNat ≤ 122) ∨ b.toNat = 45)

theorem nameByteOk_iff (b : w8) : nameByteOk b = true ↔
    ((48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨ (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨
      (97 ≤ b.toNat ∧ b.toNat ≤ 122) ∨ b.toNat = 45) := by
  unfold nameByteOk; simp

/-- `kindNames()`: the kinds' names, in the kinds' order. -/
def kindNameList : List GoString :=
  [go!"kv", go!"watch", go!"cache", go!"compact", go!"putget", go!"auth", go!"authLease",
    go!"leaseRead", go!"leaseCatchup", go!"leaseExpiry", go!"durable"]

/-- A known kind: `0 <= k < len(kindNames())` (signed). -/
def kindKnown (k : w64) : Prop := 0 ≤ sint.Z k ∧ sint.Z k < 11

instance (k : w64) : Decidable (kindKnown k) := by unfold kindKnown; infer_instance

/-- `Kind.String()`: the kind's name, `"unknown"` for an unknown kind. -/
def kindName (k : w64) : GoString :=
  if kindKnown k then kindNameList.getD (sint.nat k) [] else go!"unknown"

/-- `writesKeys(k)`. -/
def kindWritesKeys (k : w64) : Bool := decide (k ≠ W64 7 ∧ k ≠ W64 8 ∧ k ≠ W64 9)

/-- `needsSoleWriter(k)`. -/
def kindNeedsSoleWriter (k : w64) : Bool :=
  decide (k = W64 0 ∨ k = W64 1 ∨ k = W64 2 ∨ k = W64 5 ∨ k = W64 6)

/-- `alone(k)`, `NeedsAuth(k)`. -/
def kindAlone (k : w64) : Bool := decide (k = W64 5 ∨ k = W64 6)

/-- `grantsLeases(k)`. -/
def kindGrantsLeases (k : w64) : Bool := decide (k = W64 6 ∨ k = W64 8 ∨ k = W64 9)

/-- `needsNoExpiry(k)`. -/
def kindNeedsNoExpiry (k : w64) : Bool := decide (k = W64 6 ∨ k = W64 8)

/-- `NodeCount(w)`. -/
def Workload.goNodeCount (w : Workload) : w64 :=
  if w.kind = W64 0 ∨ w.kind = W64 1 ∨ w.kind = W64 2 then w.clients
  else if w.kind = W64 5 then W64 4 else W64 0

/-- `boundsOk(w)` (Go's `int` arithmetic: `(2^60-1)/c` is a positive constant over a positive `c`,
so Go's quotient is the integer one). -/
def Workload.goBoundsOk (w : Workload) : Prop :=
  let c := sint.Z w.clients
  let o := sint.Z w.ops
  if w.kind = W64 0 then 0 ≤ c ∧ c < 2 ^ 31 ∧ 0 ≤ o ∧ (c = 0 ∨ o ≤ (2 ^ 60 - 1) / c)
  else if w.kind = W64 1 ∨ w.kind = W64 2 then
    0 ≤ c ∧ c < 2 ^ 31 ∧ 0 ≤ o ∧ (c = 0 ∨ o ≤ (2 ^ 62 - 1) / c)
  else if w.kind = W64 10 then 0 ≤ c ∧ c ≤ 256
  else True

instance (w : Workload) : Decidable w.goBoundsOk := by unfold Workload.goBoundsOk; infer_instance

/-- What `compatible(ws)` returning `true` says: the kinds distinct; a kind that is `alone` the only
workload; beside a kind that `needsSoleWriter` (at another index) no kind that `writesKeys`; not both
`LeaseExpiry` and a kind that `needsNoExpiry`. -/
def goCompatible (ws : List Workload) : Prop :=
  (ws.map Workload.kind).Nodup ∧
  (∀ w ∈ ws, kindAlone w.kind = true → ws.length = 1) ∧
  (∀ (i j : Nat) (w x : Workload), ws[i]? = some w → ws[j]? = some x → i ≠ j →
    kindNeedsSoleWriter w.kind = true → kindWritesKeys x.kind = false) ∧
  ¬ ((∃ w ∈ ws, w.kind = W64 9) ∧ ∃ w ∈ ws, kindNeedsNoExpiry w.kind = true)

/-- What `IdsOk(d)` returning `true` says of the ids `ids` (`memberIDs(d)`): their 16 low bits
nonzero and distinct, and, if a workload grants leases, their 15 low bits distinct. -/
def goIdsOk (ids : List w64) (ws : List Workload) : Prop :=
  (ids.map (fun id => uint.Z id % 2 ^ 16)).Nodup ∧ (∀ id ∈ ids, uint.Z id % 2 ^ 16 ≠ 0) ∧
  ((∃ w ∈ ws, kindGrantsLeases w.kind = true) → leaseIdsApart ids)

end etcd_dist
end EtcdGrove
end Perennial

end
