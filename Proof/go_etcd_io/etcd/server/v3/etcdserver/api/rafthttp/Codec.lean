/-
**rafthttp's message codecs at the bytes** (2026-10-22, rafthttp stage 3): the vocabulary of the
specs of `messageEncoder.encode` and `messageDecoder.decodeLimit` (`msg_codec.go`). Lean-first;
the plan: `notes/rafthttp-plan.md`, stage 3.

* `writerAt wi Wr A` (persistent): the contract of the `io.Writer` `wi` that the encoder writes to,
  by `Wr bs`, the bytes `bs` written so far, and the permission `A`: `Write(p)` of a slice holding
  `chunk`, given `□ A (bs ++ chunk)`, appends the first `k` bytes of `chunk` and returns `k`, all
  of them unless the error is non-nil, an error whose `Error()` returns (`http.errStrOk`, 2026-10-23,
  stage 5b: the stream writer logs it) (the storage backend's `writerOk` with a permission: a
  response stream's writer may write only what the response protocol allows,
  `Proof/net/http/Boundary.lean`).
* `writerAtF nf wi Wr A` (persistent; 2026-10-24, rafthttp stage 7d): `writerAt`'s contract, and
  when `nf` (never fails) every error `nil`: a `bytes.Buffer`'s `Write`, the snapshot sender's
  envelope (`createSnapBody`: its `lg.Panic` on an encoding error is then unreachable).
  `writerAt` is `writerAtF false` (`writerAt_F`).
* `readFullAt r Rd B` (persistent): the contract of `io.ReadFull` of the reader `r` the decoder
  reads from, by `Rd rs`, the bytes `rs` read so far, and what is known of them, `B`: `ReadFull`
  into a slice of `xs.length` bytes reads `ys`, all of them unless the error is non-nil, and
  `□ B (rs ++ ys)` (a response body's: some response the protocol allows extends them), with an
  error whose `Error()` returns (2026-10-23, stage 5c: the stream reader logs it).
* `msgFrame bs`: a message's frame, its encoding `bs` after its length as eight big-endian bytes.
* `swMsgBound ml st` (persistent; stage A of the per-type models): the message `ml` frozen at a
  wire content of `st` of size below `2^47` (what the encoders size and marshal).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PbMessage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PerTypeMessage
public import Proof.encoding.binary.Defs
public import Proof.net.http.Boundary
public import Proof.errors.NewVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `io.Writer` `wi`'s contract with the permission `A`** (persistent; see the file
header). -/
def writerAt (wi : GoInterfaceOk) (Wr A : List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (p : GoSlice) (dq : DFrac) (chunk bs : List w8),
    {{ p ↦*{dq} chunk ∗ Wr bs ∗ □ A (bs ++ chunk) }}
      (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ k : Nat, p ↦*{dq} chunk ∗ Wr (bs ++ chunk.take k) ∗
          ⌜sint.Z n = k ∧ k ≤ chunk.length ∧ (err = GoInterface.nil → k = chunk.length)⌝ ∗
          http.errStrOk err }})

instance writerAt_persistent (wi : GoInterfaceOk) (Wr A : List w8 → IProp GF) :
    Persistent (writerAt wi Wr A) := by
  unfold writerAt; infer_instance

/-- **The `io.Writer` `wi`'s contract with the permission `A`, never failing if `nf`**
(persistent; see the file header). -/
def writerAtF (nf : Bool) (wi : GoInterfaceOk) (Wr A : List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (p : GoSlice) (dq : DFrac) (chunk bs : List w8),
    {{ p ↦*{dq} chunk ∗ Wr bs ∗ □ A (bs ++ chunk) }}
      (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ k : Nat, p ↦*{dq} chunk ∗ Wr (bs ++ chunk.take k) ∗
          ⌜sint.Z n = k ∧ k ≤ chunk.length ∧ (err = GoInterface.nil → k = chunk.length)⌝ ∗
          http.errStrOk err ∗ ⌜nf = true → err = GoInterface.nil⌝ }})

instance writerAtF_persistent (nf : Bool) (wi : GoInterfaceOk) (Wr A : List w8 → IProp GF) :
    Persistent (writerAtF nf wi Wr A) := by
  unfold writerAtF; infer_instance

/-- A writer's contract is that of one that may fail. -/
theorem writerAt_F (wi : GoInterfaceOk) (Wr A : List w8 → IProp GF) :
    writerAt (GF := GF) wi Wr A ⊢ writerAtF false wi Wr A := by
  unfold writerAt writerAtF
  iintro #Hw !> %p %dq %chunk %bs %Φ !> Hpre HΦ
  wp_apply Hw $$ [$Hpre] as %n %err ⟨%k, Hp, HWr, %Hk, #Herr⟩
  iapply HΦ
  iexists k
  iframe; iframe #
  ipureintro
  exact ⟨Hk, fun h => absurd h (by decide)⟩

/-- **`io.ReadFull` of the reader `r`'s contract, with what is known of the bytes read, `B`**
(persistent; see the file header). -/
def readFullAt (r : GoInterface) (Rd B : List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (p : GoSlice) (xs rs : List w8),
    {{ p ↦* xs ∗ Rd rs }}
      (App (App (Val (@! _root_.Perennial.io.ReadFull)) (Val #r)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, p ↦* (ys ++ xs.drop ys.length) ∗ Rd (rs ++ ys) ∗ □ B (rs ++ ys) ∗
          ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length ∧
            (err = GoInterface.nil → ys.length = xs.length)⌝ ∗ http.errStrOk err }})

instance readFullAt_persistent (r : GoInterface) (Rd B : List w8 → IProp GF) :
    Persistent (readFullAt r Rd B) := by
  unfold readFullAt; infer_instance

/-- **A message's frame** (`messageEncoder`'s): its encoding `bs` after its length, eight
big-endian bytes. -/
def msgFrame (bs : List w8) : List w8 := u64Be (W64 bs.length) ++ bs

/-- **A message's wire content, bounded** (stage A of the per-type models; the Scope's `Z`, which
raft-entsize is to derive from its `out_size`): the frozen message `ml` holds a wire content of
`st` whose size is below `2^47` bytes. What the encoders size and marshal (`proto.Size`,
`MarshalAppend`, `MustMarshalMessage` take the content), and what bounds the sizes the stream
writer sums (2049 of them stay below `2^62`). Derived from the sender's content (`msgSzC`,
raft-entsize; until then the trust-boundary axiom `swMsgBound_phys`). The content's snapshot `ConfState` has no unknown fields
(`MsgC.csUfNil`, the sender's fact: raft's `csPts` fixes them to none), what the receiver's decoded
message needs (`MsgEnc`). -/
def swMsgBound (ml : Loc) (st : MsgSt) : IProp GF :=
  iprop(∃ c : MsgC, msgRoC ml c ∗ ⌜c.model = st ∧ c.csUfNil ∧ msgSize c < 2 ^ 47⌝)

instance swMsgBound_persistent (ml : Loc) (st : MsgSt) :
    Persistent (swMsgBound (GF := GF) ml st) := by
  unfold swMsgBound; infer_instance

end defs

/-- **`bs` decodes to the content `c`** (raft-entsize §4, 2026-11-10: `proto.Unmarshal`'s D1 and D2
at a message): `c` is a wire content of `bs` whose unknown fields are valid and whose snapshot's conf
state has none, of which `bs` is the encoding, at most twice as large as `bs` (D1), and the one
content that marshals, with valid unknown fields, of which `bs` is the encoding (D2): what the
message decoders give of the message they decode. -/
def MsgDecC [GooseExts] (c : MsgC) (bs : List w8) : Prop :=
  MsgWireOk c.model bs ∧ (∀ q ∈ c.levels, ufWire q.1 q.2) ∧ c.csUfNil ∧ bs = msgEncC c ∧
    msgSize c ≤ 2 * bs.length ∧
    ∀ c₀ : MsgC, MsgMarshals c₀.model → (∀ q ∈ c₀.levels, ufWire q.1 q.2) → bs = msgEncC c₀ → c₀ = c

/-- A content whose model has no responses has none. -/
theorem MsgC.resps_nil_of_model [GooseExts] {c : MsgC} (h : c.model.resps = []) : c.resps = [] := by
  simpa [MsgC.model] using h

/-- A message of another's wire fields with no responses is that one's fields with none. -/
theorem MsgSt.eq_of_wire [GooseExts] {st st0 : MsgSt} (hw : wireOf st0 = wireOf st) (hr : st.resps = []) :
    st = ⟨st0.msg, st0.ents, st0.snap, st0.ctx, []⟩ := by
  cases st; cases st0
  simp only [wireOf, MsgWire.mk.injEq] at hw
  simp_all

theorem MsgDecC.enc [GooseExts] {c : MsgC} {bs : List w8} (h : MsgDecC c bs) : MsgEnc c.model bs :=
  ⟨c, rfl, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- A decoded content has no responses (it marshals). -/
theorem MsgDecC.resps [GooseExts] {c : MsgC} {bs : List w8} (h : MsgDecC c bs) : c.resps = [] :=
  MsgC.resps_nil_of_model h.1.1

/-- A content decoded from at most `2^29` bytes (rafthttp's `readBytesLimit`) is of bounded size
(D1's factor 2). -/
theorem MsgDecC.sizeOk [GooseExts] {c : MsgC} {bs : List w8} (h : MsgDecC c bs)
    (hl : bs.length ≤ 2 ^ 29) : msgSizeOk c :=
  msgSizeOk_of_size c (by have := h.2.2.2.2.1; omega) h.resps

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
open Iris.ProofMode

/-- An `errors.New` error's `Error()` returns (`errorsNewVar`'s method fact), and it is a leaf of
an error tree (`ErrorStringLeaf`). -/
theorem errorString_errStrOk [_root_.Perennial.errors.Assumptions] (x : Loc) (msg : GoString) :
    ⊢ (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
        WP (App (Val #(methods (go.GoType.PointerType _root_.Perennial.errors.errorString.ty)
          go!"Error" #x)) (Val #())) {{ Φ }}) -∗
      http.errStrOk (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  iintro #HM
  unfold http.errStrOk
  iright
  iexists ⟨go.GoType.PointerType _root_.Perennial.errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %Φ HΦ
    iapply HM
    inext
    iapply HΦ
  have hl := errorString_leaf x
  unfold http.errTreeOk
  iintro !> %target %Ht
  iexists (· = interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x),
    (fun _ => False)
  isplitr
  · ipureintro
    exact ⟨rfl, _root_.Perennial.errors.treeTyped_pointer _ _ hl.1⟩
  iapply _root_.Perennial.errors.errorIsTree_leaf _ _ _ hl.2.1 hl.2.2

end lemmas

end EtcdGrove
end Perennial
