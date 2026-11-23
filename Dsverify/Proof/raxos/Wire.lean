/-
The wire-level definitions shared by the proxy (package `proxy`) and the kit's client (package
`kit`): `leNum` (the 8-byte length prefix of a `ClientBatch` frame) and `registerProto`'s spec.
`ClientBatch.Marshal`'s spec is `examples/quepaxanet/KitWire.lean`'s `cbMarshal.spec`,
`ClientBatch.Unmarshal`'s `Proxy/NetUnmarshal.lean`'s `unmarshalB.spec` (the lab's two specs that
stood here, unused, are gone).

Changed against the lab (notes/dsv-quepaxa.md): `bufio` is origin/dsv-bufio's
(`EtcdGrove.bufio.ownBufWriter`/`ownBufReader`, with the writer's error evidence `Ew` and size
`sz`, the reader's read condition `Pre` (here any read is allowed) and stream state `S`); the
codec's facts (`codecSet`, `kitCodecOk`) are gone (protobuf's `Marshal`/`Unmarshal` are hypotheses,
`Hyp.lean`); `registerProto` is a no-op (`kit.go`), its spec `True`.
-/
module

public import Dsverify.Proof.raxos.Replica
public import Dsverify.Proof.raxos.examples.quepaxanet.Base
public import Proof.bufio.Own

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open EtcdGrove (bufio.ownBufWriter bufio.ownBufReader)

/-- The little-endian 64-bit number of 8 bytes. -/
def leNum (bs : List w8) : Nat := (bs.zipIdx.map (fun p => p.1.toNat * 2 ^ (8 * p.2))).sum

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `registerProto()`: a no-op here (`kit.go`: the Go build runs the real protobuf). -/
abbrev registerProto.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet }}
    (App (Val (@! raxos.examples.quepaxanet.registerProto)) (Val #()))
  {{ RET #(); True }}

end specs

end Perennial.raxos
