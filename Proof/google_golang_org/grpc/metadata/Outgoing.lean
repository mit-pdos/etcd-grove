/-
**A context's outgoing metadata** (grpc's `metadata`, names-only; the auth plan's E2f,
2026-10-25). Lean-first (no Rocq counterpart).

The counterpart of `incomingOf` (`Incoming.lean`) on a call's side: the metadata a context
carries under grpc's outgoing-metadata key (`metadata.NewOutgoingContext`,
`AppendToOutgoingContext`; read by `FromOutgoingContext` and by grpc's transport, which sends it as
the call's header fields), a function of the context value (`outgoingOf`, opaque) for the same
reason: a context is immutable. `mdAdd md k v` is the metadata with `v` appended to the values of
`k` (as `AppendToOutgoingContext(ctx, k, v)` adds it, for a lower-case `k`); `mdSet md k vs`, with
them set to `vs` (`MD.Set`). The client's auth
contract (`examples/authkv/ClientAuth.lean`, C1-C4) is stated over the two.
-/
module

public import Proof.google_golang_org.grpc.metadata.Incoming

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace metadata

/-- **The outgoing metadata of the context `ctx`** (opaque, see the file header): `none` if it
has none, else each key's values. -/
opaque outgoingOf [GooseExts] : GoInterface → Option (GoString → Option (List GoString))

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

/-- A key with no upper-case ASCII letter (grpc lower-cases the keys it is given). -/
def lowerKey (k : GoString) : Prop := ∀ b ∈ k, ¬ (W8 65 ≤ b ∧ b ≤ W8 90)

end metadata
end EtcdGrove
end Perennial
