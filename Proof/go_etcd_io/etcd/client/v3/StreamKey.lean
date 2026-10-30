/-
**The watch stream's key** (G2, 2026-10-30; `notes/g2-watch-auth.md`): the string
`streamKeyFromCtx` computes from a context's outgoing metadata (`client/v3/watch.go:1102-1107`),
which the watcher uses to share one gRPC stream among the watches whose contexts carry the same
metadata. Opaque, with two trusted laws: a faithful `fmt.Sprintf("%+v", ...)` of a map needs its
sorted finite key set, which the function-valued `GrpcMd` does not carry. The key collides
(`issues/etcd-watch-stream-key-collision.md`); the laws hold only where it does not. Lean-first
(no Rocq counterpart).
-/
module

public import Proof.google_golang_org.grpc.metadata.Outgoing
public import Proof.google_golang_org.grpc.InvGrpc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **The key `streamKeyFromCtx` computes from the outgoing metadata `m`**
(`metadata.outgoingOf`'s view: what `FromOutgoingContext` returns): Go's
`fmt.Sprintf("%+v", map[string][]string(md))` (`map[k1:[v1 v2] k2:[...]]`, keys sorted, each
value list joined by spaces) when there is metadata, `""` when there is none. -/
opaque streamKeyOf [GooseExts] : GrpcMd → GoString

/-- **Only "no metadata" gives the empty key** (trusted; G2's (c)): any map, even an empty one,
prints as `map[...]`, which is not `""`. -/
axiom streamKeyOf_none [GooseExts] (m : GrpcMd) : streamKeyOf m = streamKeyOf none → m = none

/-- **A one-entry map's key determines its entry's values** (trusted; G2's (c)), for a lower-case
key `k`, a non-empty value `v` (Go prints `[]` and `[""]` alike) and a key and value free of ` `,
`:`, `[` and `]`: the printed `map[k:[v]]` has no
space, so the other map has one entry with one value (Go joins entries and values with spaces), and
its key and value are then read back from the only `:` and brackets (checked against `%+v`'s
format in G2's review round 3; the `axiom` skill's review, `notes/axiom-review/g2-streamkey.md`,
added `v ≠ ""` and made `lowerKey` ASCII). -/
axiom streamKeyOf_single [GooseExts] (m : GrpcMd) (k v : GoString) (hk : metadata.lowerKey k)
    (hs : ∀ b ∈ k ++ v, b ∉ [W8 32, W8 58, W8 91, W8 93]) (hv : v ≠ go!"") :
    streamKeyOf m = streamKeyOf (metadata.mdAdd none k v) → metadata.mdVals m k = [v]

end EtcdGrove
end Perennial
