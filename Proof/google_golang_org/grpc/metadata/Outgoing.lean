/-
**A context's outgoing metadata** (grpc's `metadata`, names-only; the auth plan's E2f,
2026-10-25). Lean-first (no Rocq counterpart).

The counterpart of `incomingOf` (`Incoming.lean`) on a call's side: the metadata a context
carries under grpc's outgoing-metadata key (`metadata.NewOutgoingContext`,
`AppendToOutgoingContext`; read by `FromOutgoingContext` and by grpc's transport, which sends it as
the call's header fields), a function of the context value (`outgoingOf`, opaque) for the same
reason: a context is immutable. `mdAdd md k v` is the metadata with `v` appended to the values of
`k` (as `AppendToOutgoingContext(ctx, k, v)` adds it, for a lower-case `k`). The client's auth
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
opaque outgoingOf [FfiSyntax] : GoInterface → Option (GoString → Option (List GoString))

/-- Metadata (`none`: no metadata) with `v` appended to the values of the key `k`. -/
def mdAdd (md : Option (GoString → Option (List GoString))) (k v : GoString) :
    Option (GoString → Option (List GoString)) :=
  some fun k' =>
    if k' = k then some (((md.bind fun m => m k).getD []) ++ [v]) else md.bind fun m => m k'

/-- The values of the key `k` in the metadata `md` (none: `[]`). -/
def mdVals (md : Option (GoString → Option (List GoString))) (k : GoString) : List GoString :=
  (md.bind fun m => m k).getD []

theorem mdVals_mdAdd (md : Option (GoString → Option (List GoString))) (k v : GoString) :
    mdVals (mdAdd md k v) k = mdVals md k ++ [v] := by
  simp [mdVals, mdAdd]

/-- A key with no upper-case ASCII letter (grpc lower-cases the keys it is given). -/
def lowerKey (k : GoString) : Prop := ∀ b ∈ k, ¬ (W8 65 ≤ b ∧ b ≤ W8 90)

end metadata
end EtcdGrove
end Perennial
