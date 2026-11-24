/-
The vocabulary of the specs of `net/http/internal`'s chunked writer (Go 1.27.3's `chunked.go`, the
toolchain's code, translated with its bodies; phase 7 S5, `notes/phase7-plan.md`, "S5 draft
signatures", §3), what the Transport writes a request body of unknown length through:

* `chunkWire xs`: the wire of one chunk of the bytes `xs`, `hex(len xs) ++ "\r\n" ++ xs ++ "\r\n"`
  (`fmt`'s `%x`: `hexadecimal`, lowercase, no `0x`), nothing for no bytes (`Write` sends no empty
  chunk: it would read as the end);
* `lastChunk`: what `Close` writes, `"0\r\n"` (the trailer and the final `"\r\n"` are the
  Transport's, `transferWriter.writeBody`);
* `chunkSink wi W B` (persistent): what the chunked writer needs of its `Wire` `wi`, with the
  client's state `W out` (`out` the bytes the sink has accepted) and broken state `B err` (after a
  failed call, with its error): a `Write` of some bytes accepts all of them (`(len, nil)`) or fails;
  the same for `io.WriteString` of a string (`EtcdGrove.io.stringWriteOk`: `WriteString` when the
  dynamic type has one, as `*bufio.Writer` has); and, when `wi` is a `*FlushAfterChunkWriter`, its
  `Flush` (promoted from its `*bufio.Writer`) keeps `W out` or fails (its value a pointer);
* `chunkedW cw wi` (exclusive, given back by `Write` and `Close`): the `*chunkedWriter` at `cw` has the `Wire` `wi` (never written:
  `NewChunkedWriter`'s).
-/
module

public import Net.GeneratedProof.net.http.internal
public import Spec.io.WriteString
public import Perennial.Proof.fmt.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace net.http.internal

section pure

/-- See the file header. -/
def chunkWire (xs : List w8) : List w8 :=
  if xs = [] then [] else fmt.hexadecimal xs.length ++ go!"\r\n" ++ xs ++ go!"\r\n"

/-- See the file header. -/
def lastChunk : List w8 := go!"0\r\n"

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What a sink call gives back: success, the bytes `ys` accepted after `out`, or failure. -/
def sinkPost (W : List w8 → IProp GF) (B : GoInterface → IProp GF) (out ys : List w8) (n : w64)
    (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil ∧ sint.Z n = ys.length⌝ ∗ W (out ++ ys)) ∨
    (⌜err ≠ interface.nil⌝ ∗ B err))

/-- See the file header. -/
def chunkSink (wi : GoInterfaceOk) (W : List w8 → IProp GF) (B : GoInterface → IProp GF) :
    IProp GF :=
  iprop((□ ∀ (out : List w8) (p : GoSlice) (xs : List w8) (dq : DFrac),
      {{ W out ∗ p ↦*{dq} xs }}
        (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #p))
      {{ (n : w64) (err : GoInterface), RET (PairV #n #err); p ↦*{dq} xs ∗
          sinkPost W B out xs n err }}) ∗
    (□ ∀ (out : List w8) (s : GoString),
      EtcdGrove.io.stringWriteOk wi s (W out) (sinkPost W B out s)) ∗
    ⌜wi.ty = go.GoType.PointerType FlushAfterChunkWriter.ty → ∃ bw : Loc, wi.v = #bw⌝ ∗
    (□ ∀ (bw : Loc) (out : List w8),
      ⌜wi = ⟨go.GoType.PointerType FlushAfterChunkWriter.ty, #bw⟩⌝ →
      {{ W out }}
        (App (Val #(methods (go.GoType.PointerType FlushAfterChunkWriter.ty) go!"Flush" #bw))
          (Val #()))
      {{ (err : GoInterface), RET #err; sinkPost W B out [] (W64 0) err }}))

instance chunkSink_persistent (wi : GoInterfaceOk) (W : List w8 → IProp GF)
    (B : GoInterface → IProp GF) : Persistent (chunkSink wi W B) := by
  unfold chunkSink; infer_instance

/-- See the file header. -/
def chunkedW (cw : Loc) (wi : GoInterfaceOk) : IProp GF :=
  iprop(cw ↦ ({ Wire' := interface.ok wi } : chunkedWriter))

end defs

end net.http.internal
end Perennial
