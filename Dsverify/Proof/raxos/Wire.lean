/-
The wire-level specs shared by the proxy (package `proxy`) and the kit's client (package `kit`):
`ClientBatch.Marshal` and `.Unmarshal` (`proto/client/clientwrapper.go`) over `bufio`'s
buffered writer and reader, and `registerProto` (interface of stage 1, `notes/stage1-plan.md`).

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

/-- `t.Marshal(w)` on a `*bufio.Writer` `bw` (as an `io.Writer`): for a well-formed batch, its
8-byte length and encoding appended to the writer's stream (it returns only with an encoding
that fits a Go slice: `proto.Marshal` succeeds on every well-formed batch and returns a slice;
one that does not fit is an angelic exit of the encoder's `append`), which must allow them (a prefix of
them on an error); for one the codec rejects (invalid UTF-8), an error and nothing written. -/
abbrev ClientBatch.Marshal.spec : Prop :=
  ∀ (t : Loc) (dq : DFrac) (b : Batch) (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF)
    (Ew : GoInterface → IProp GF) (sz : Nat) (sent pend : List w8) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.proto.client ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ repCB t dq b ∗
      bufio.ownBufWriter bw wi J Q Ew sz sent pend err ∗
      □ (⌜batchOk b ∧ (encBatch b).length < 2 ^ 63⌝ →
          Q (sent ++ pend ++ le8 (encBatch b).length ++ encBatch b)) }}
    (App (Val (t @!! go.GoType.PointerType raxos.proto.client.ClientBatch.ty @!! go!"Marshal"))
      (Val #(interface.mkOk (go.GoType.PointerType Perennial.bufio.Writer.ty) #bw)))
  {{ (e : GoInterface), RET #e; repCB t dq b ∗
      ∃ (k : Nat) (sent' pend' : List w8) (e' : GoInterface),
        ⌜sent' ++ pend' = sent ++ pend ++ (le8 (encBatch b).length ++ encBatch b).take k ∧
          (e = interface.nil → batchOk b ∧ (encBatch b).length < 2 ^ 63 ∧
            k = (le8 (encBatch b).length ++ encBatch b).length) ∧
          (¬ (batchOk b ∧ (encBatch b).length < 2 ^ 63) → k = 0) ∧
          (batchOk b → (encBatch b).length < 2 ^ 63)⌝ ∗
        bufio.ownBufWriter bw wi J Q Ew sz sent' pend' e' }}

/-- `t.Unmarshal(r)` on a `*bufio.Reader` `br` (as an `io.Reader`, over a reader whose every read
is allowed), into a fresh `ClientBatch`: it reads an 8-byte length (below `2^63` if read whole, as
the stream promises) and that many bytes; on success they encode the decoded batch `b` (any
well-formed batch whose encoding they are is `b`). -/
abbrev ClientBatch.Unmarshal.spec : Prop :=
  ∀ (t : Loc) (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF) (R : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.proto.client ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ t ↦ (zero_val raxos.proto.client.ClientBatch) ∗
      bufio.ownBufReader br ri Pre S E R ∗ ⌜∀ r m, 0 < m → Pre r m⌝ ∗
      □ (∀ d e, S (R ++ d ++ e) -∗ ⌜d.length = 8 → leNum d < 2 ^ 63⌝) }}
    (App (Val (t @!! go.GoType.PointerType raxos.proto.client.ClientBatch.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType Perennial.bufio.Reader.ty) #br)))
  {{ (e : GoInterface), RET #e; ∃ data : List w8, bufio.ownBufReader br ri Pre S E (R ++ data) ∗
      (⌜e ≠ interface.nil⌝ ∨
       ∃ (bs : List w8) (b : Batch), ⌜e = interface.nil ∧ data = le8 bs.length ++ bs ∧
         bs.length < 2 ^ 63 ∧
         ∀ b0, batchOk b0 → encBatch b0 = bs → b = b0⌝ ∗ repCB t (DFrac.own 1) b) }}

/-- `registerProto()`: a no-op here (`kit.go`: the Go build runs the real protobuf). -/
abbrev registerProto.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.examples.quepaxanet }}
    (App (Val (@! raxos.examples.quepaxanet.registerProto)) (Val #()))
  {{ RET #(); True }}

end specs

end Perennial.raxos
