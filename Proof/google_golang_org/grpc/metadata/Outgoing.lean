/-
**Outgoing metadata values** (grpc's `metadata`, names-only; the auth plan's E2f, 2026-10-25).
Lean-first (no Rocq counterpart).

The call side's counterpart of a context's incoming metadata: the metadata a context carries under
grpc's outgoing-metadata key (`metadata.NewOutgoingContext`, `AppendToOutgoingContext`; read by
`FromOutgoingContext` and by grpc's transport, which sends it as the call's header fields). Which
metadata a context carries is the per-run relation `metadata.outMD ctx md`
(`Proof/context/LibKeysChain.lean`; errdesc stage 1, 2026-11-20: until then the opaque pure function
`metadata.outgoingOf : GoInterface → Option (...)` declared here, a function of the context value,
which no implementation can meet for the contexts it allocates, `notes/errdesc-ghost-plan.md`).
This file keeps the pure operations on metadata values: `mdAdd md k v` is the metadata with `v`
appended to the values of `k` (as `AppendToOutgoingContext(ctx, k, v)` adds it, for a lower-case
`k`); `mdSet md k vs`, with them set to `vs` (`MD.Set`). The client's auth contract
(`examples/lib/authwork/ClientAuth.lean`, C1-C4) is stated over `outMD` and `ctxInMD`. A raw `MD` whose
keys collide up to case (a literal map given to `NewOutgoingContext`, where grpc's result depends on
map order) is outside the model (G2, 2026-10-30: `streamKeyOf`'s laws rely on this reading).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace metadata

/-- Metadata (`none`: no metadata) with `v` appended to the values of the key `k`. -/
def mdAdd (md : Option (GoString → Option (List GoString))) (k v : GoString) :
    Option (GoString → Option (List GoString)) :=
  some fun k' =>
    if k' = k then some (((md.bind fun m => m k).getD []) ++ [v]) else md.bind fun m => m k'

/-- Metadata (`none`: no metadata) with the values of the key `k` set to `vs` (as `MD.Set(k,
vs...)` on a copy sets them, or `Pairs(k, v)` makes them from none, for a lower-case `k`; the auth
plan's E3zc: what `clientv3`'s `withVersion` does to the API version's key). -/
def mdSet (md : Option (GoString → Option (List GoString))) (k : GoString) (vs : List GoString) :
    Option (GoString → Option (List GoString)) :=
  some fun k' => if k' = k then some vs else md.bind fun m => m k'

/-- The values of the key `k` in the metadata `md` (none: `[]`). -/
def mdVals (md : Option (GoString → Option (List GoString))) (k : GoString) : List GoString :=
  (md.bind fun m => m k).getD []

theorem mdVals_mdSet_ne (md : Option (GoString → Option (List GoString))) (k k' : GoString)
    (vs : List GoString) (h : k' ≠ k) : (mdSet md k vs).bind (fun m => m k') = md.bind fun m => m k' := by
  simp [mdSet, h]

theorem mdVals_mdAdd (md : Option (GoString → Option (List GoString))) (k v : GoString) :
    mdVals (mdAdd md k v) k = mdVals md k ++ [v] := by
  simp [mdVals, mdAdd]

/-- **Metadata as grpc delivers it** (the auth plan's C1, 2026-10-28): without the keys that have no
values (grpc writes one header field per value, so such a key is not sent). -/
def mdNorm (md : Option (GoString → Option (List GoString))) :
    Option (GoString → Option (List GoString)) :=
  md.map fun m k => match m k with
    | some [] => none
    | v => v

/-- A key of ASCII bytes with no upper-case letter: one grpc's `strings.ToLower` leaves unchanged.
(Excluding only `A`-`Z` was not enough: `ToLower` lower-cases all of Unicode, `É` to `é`, and
replaces invalid UTF-8; G2's axiom review, `notes/axiom-review/g2-streamkey.md`.) -/
def lowerKey (k : GoString) : Prop := ∀ b ∈ k, b < W8 128 ∧ ¬ (W8 65 ≤ b ∧ b ≤ W8 90)

end metadata
end EtcdGrove
end Perennial
