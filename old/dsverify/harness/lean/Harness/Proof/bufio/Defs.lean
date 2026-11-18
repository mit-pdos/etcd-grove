/-
The vocabulary of the specs of Go's `bufio` (`Reader.lean`, `Writer.lean`): the underlying
`io.Reader` / `io.Writer` (an interface value) given by its own `Read` / `Write` spec, and the
buffered reader's and writer's states.

**The underlying stream.** The specs are generic over the object under the buffer: an interface
value whose method meets a spec stated over an abstract resource indexed by the stream so far.
* `readerOk rd I` (persistent): `rd` is a non-nil `io.Reader` (not itself a `*bufio.Reader`,
  which `NewReader` would return as is) whose `Read(b)`, from `I R` (`R` read so far) and `b`'s
  bytes `bs`, returns `n = len(data)` for the next bytes `data` of the stream (at most
  `len(b)`; possibly none, also without an error), in `b`'s first `n` elements, with
  `I (R ++ data)`, and an error that is `nil` or has some message (`net.rpc.errAny`; `errWf`:
  a pointer-typed error holds a pointer). Bytes and an error may come together (Go's
  `io.Reader` contract).
* `writerOk wr J Q` (persistent): `wr` is a non-nil `io.Writer` (not a `*bufio.Writer`) whose
  `Write(b)`, from `J W` (`W` written so far), the obligation `□ Q (W ++ bs)` for `b`'s bytes
  `bs`, returns `n = k` with `J (W ++ bs.take k)`, `k ≤ len(bs)`, `k = len(bs)` when the error is
  `nil` (Go's `io.Writer` contract: a short write has an error), the error `nil` or with some
  message. `Q` is prefix-closed (`prefixClosed`): the buffer may send any prefix of what it was
  given, when it fills.
`Net.lean` proves both of a `net.Conn` holding a `*TCPConn` (`I = recvTok`, `J = sendTok`,
`Q = P cid`).

**The buffered reader** `ownReader br rd I R`: `br` is a `*bufio.Reader` over `rd`; `R` is what
it has returned so far; the underlying stream has delivered `R ++ pend` (`I (R ++ pend)`, held
by the reader, visible to the client), `pend` buffered; an error of the underlying reader may be
pending (it is returned once the buffered bytes are). So the bytes the reader returns are a
prefix of what the underlying stream delivers, in order.

**The buffered writer** `ownWriter bw wr J Q sent pend err`: `bw` is a `*bufio.Writer` over
`wr`; `sent` has gone to the underlying writer (`J sent`, visible to the client), `pend` is
buffered, not sent; `□ Q (sent ++ pend)` (what the buffer will send is allowed); `err` is the
writer's sticky error (`nil` while healthy; once not `nil`, every later `Write`, `WriteByte` and
`Flush` returns it and sends nothing).
-/
module

public import Harness.Proof.bufio.Base
public import Harness.Proof.net.rpc.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std NetConn

namespace bufio

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `Q` holds of every prefix of a stream it holds of (persistent). -/
def prefixClosed (Q : List w8 → IProp GF) : IProp GF :=
  iprop(□ (∀ (x y : List w8), Q (x ++ y) -∗ Q x))

/-- The prefix closure of a stream predicate: `W` is a prefix of a stream `ext` with
`□ Q ext` (`W` empty included). -/
def prefixClose (Q : List w8 → IProp GF) (W : List w8) : IProp GF :=
  iprop(⌜W = []⌝ ∨ ∃ ext : List w8, ⌜W <+: ext⌝ ∗ □ Q ext)

/-- A non-nil error of a pointer type holds a pointer (true of every error Go code makes; what
comparing it with an `errors.New` error, e.g. `err == io.EOF`, needs). -/
def errWf (err : GoInterface) : Prop :=
  ∀ e : GoInterfaceOk, err = interface.ok e → ∀ T : go.GoType, e.ty = go.GoType.PointerType T →
    ∃ l : Loc, e.v = #l

/-- An error result: `nil`, or an error with some message (and `errWf`). -/
def errOrNil (err : GoInterface) : IProp GF :=
  iprop(⌜err = interface.nil⌝ ∨ (net.rpc.errAny err ∗ ⌜errWf err⌝))

/-- The underlying `io.Reader` `rd`: see the file header (persistent). -/
def readerOk (rd : GoInterface) (I : List w8 → IProp GF) : IProp GF :=
  iprop(∃ e : GoInterfaceOk,
    ⌜rd = interface.ok e ∧ e.ty ≠ go.GoType.PointerType bufio.Reader.ty⌝ ∗
    □ ∀ (b : GoSlice) (bs : List w8) (R : List w8) (Φ : val → IProp GF),
      I R -∗ b ↦* bs -∗
      ▷ (∀ (data : List w8) (err : GoInterface), ⌜data.length ≤ bs.length⌝ -∗
          b ↦* (data ++ bs.drop data.length) -∗ I (R ++ data) -∗ errOrNil err -∗
          Φ (PairV #(W64 data.length) #err)) -∗
      WP (App (Val #(methods e.ty go!"Read" e.v)) (Val #b)) {{ Φ }})

/-- The underlying `io.Writer` `wr`: see the file header (persistent). -/
def writerOk (wr : GoInterface) (J : List w8 → IProp GF) (Q : List w8 → IProp GF) :
    IProp GF :=
  iprop(∃ e : GoInterfaceOk,
    ⌜wr = interface.ok e ∧ e.ty ≠ go.GoType.PointerType bufio.Writer.ty⌝ ∗
    prefixClosed Q ∗
    □ ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (W : List w8) (Φ : val → IProp GF),
      J W -∗ □ Q (W ++ bs) -∗ b ↦*{dq} bs -∗
      ▷ (∀ (k : Nat) (err : GoInterface),
          ⌜k ≤ bs.length ∧ (err = interface.nil → k = bs.length)⌝ -∗
          b ↦*{dq} bs -∗ J (W ++ bs.take k) -∗ errOrNil err -∗
          Φ (PairV #(W64 k) #err)) -∗
      WP (App (Val #(methods e.ty go!"Write" e.v)) (Val #b)) {{ Φ }})

instance prefixClosed_persistent (Q : List w8 → IProp GF) :
    Persistent (prefixClosed (GF := GF) Q) := by
  unfold prefixClosed; infer_instance
instance errOrNil_persistent (err : GoInterface) : Persistent (errOrNil (GF := GF) err) := by
  unfold errOrNil; infer_instance
instance readerOk_persistent (rd : GoInterface) (I : List w8 → IProp GF) :
    Persistent (readerOk (GF := GF) rd I) := by
  unfold readerOk; infer_instance
instance writerOk_persistent (wr : GoInterface) (J Q : List w8 → IProp GF) :
    Persistent (writerOk (GF := GF) wr J Q) := by
  unfold writerOk; infer_instance

/-- The `*bufio.Reader` `br` over `rd` buffers `pend` and has the pending error `perr`: its
fields, its buffer `buf` (`len(buf) > 0`) holding `pend` at `[r, w)`. -/
def readerRep (br : Loc) (rd : GoInterface) (pend : List w8) (perr : GoInterface) :
    IProp GF :=
  iprop(∃ (buf : GoSlice) (r w lb lrs : w64) (pre post : List w8),
    br ↦ bufio.Reader.mk buf rd r w perr lb lrs ∗ buf ↦* (pre ++ pend ++ post) ∗
    ⌜sint.Z r = pre.length ∧ sint.Z w = pre.length + pend.length ∧
      0 < (pre ++ pend ++ post).length⌝ ∗ errOrNil perr)

/-- The `*bufio.Reader` `br` over `rd` (with `I`) has returned `R`: see the file header. -/
def ownReader (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8) :
    IProp GF :=
  iprop(∃ (pend : List w8) (perr : GoInterface), I (R ++ pend) ∗ readerRep br rd pend perr)

/-- The `*bufio.Writer` `bw` over `wr` buffers `pend` and has the error `err`: its fields, its
buffer `buf` (`len(buf) > 0`) holding `pend` at `[0, n)`. -/
def writerRep (bw : Loc) (wr : GoInterface) (pend : List w8) (err : GoInterface) : IProp GF :=
  iprop(∃ (buf : GoSlice) (n : w64) (rest : List w8),
    bw ↦ bufio.Writer.mk err buf n wr ∗ buf ↦* (pend ++ rest) ∗
    ⌜sint.Z n = pend.length ∧ 0 < (pend ++ rest).length⌝ ∗ errOrNil err)

/-- The `*bufio.Writer` `bw` over `wr` (with `J`, `Q`) has sent `sent` and buffers `pend`;
its sticky error is `err`: see the file header. -/
def ownWriter (bw : Loc) (wr : GoInterface) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) : IProp GF :=
  iprop(J sent ∗ □ Q (sent ++ pend) ∗ writerRep bw wr pend err)

end defs

end bufio

end Perennial
