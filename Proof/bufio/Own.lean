/-
**`*bufio.Reader` and `*bufio.Writer` over an `io.Reader` / `io.Writer` contract** (dsv-bufio,
2026-11-23, mit-pdos/etcd-grove#24; revised after the review on #24): the vocabulary of `bufio`'s
generic specs (`Spec/bufio/`: `NewReaderSize`, `NewReaderOk`, `Reader__ReadOk`, `Reader__ReadByte`,
`NewWriterSize`, `NewWriter`, `Writer__Flush`, `Writer__Write`, `Writer__WriteByte`,
`Writer__Available`, `Writer__Buffered`, `Writer__Size`). Nothing here is about `net`: a
connection's instances of the contracts are laws of `Net/Proof/net/ConnIo.lean`. Ported from
dsverify-lab's `Harness/Proof/bufio/Defs.lean` (its `readerOk`/`writerOk` replaced by Perennial's
`io.readerOk` and `io.streamWriterOk`, `Proof/io/StreamWriterOk.lean`; its errors "with some message" by the
contracts' evidence).

**The buffered reader** `bufio.ownBufReader br ri Pre S E R`: `br` is a `*bufio.Reader` over the
reader `ri` (`io.readerOk ri Pre S E`, held); `R` is what it has returned so far; the underlying
stream has delivered `R ++ pend` (`S (R ++ pend)`, held by the reader), `pend` buffered; an error of
the underlying reader may be pending (returned once the buffered bytes are), with its evidence at
`R ++ pend` (`bufio.errE E`: `E`'s, or `io.ErrNoProgress`'s value, which `fill` returns after 100
empty reads). Every read the buffer makes of `ri` (at most its size, from the state the stream is
in: `bufio.preUpTo S Pre`) meets `Pre`. So the bytes the reader returns are the stream's, in order,
and its errors the stream's (`Proof/bufio/ReaderLaws.lean`: a `*bufio.Reader` is itself an
`io.readerOk` reader, so Perennial's `io.ReadFull`/`io.ReadAtLeast` read through it). Clients reason
about the stream state inside through `bufio.ownBufReader_fact`, without unfolding.

`bufio.ownBufReaderE br ri Pre S E Eb szOk R` is the same reader with the evidence `Eb` of its
pending errors and a condition `szOk` on its buffer's size: `ownBufReader` is it at `bufio.errE E`
and no condition; the WAL's `bufio.ownReader` (`Proof/bufio/Defs.lean`) corresponds to it at `E`
and `(· ≤ 4096)` (`Proof/bufio/OwnReaderE.lean`). The proofs of `NewReaderSize` and `Read` are over
it, so one proof of each serves both (`bufio.NewReaderSize.specE`, `bufio.Reader.Read.specE`).

**The buffered writer** `bufio.ownBufWriter bw wi J Q Ew sz sent pend err`: `bw` is a
`*bufio.Writer` with a buffer of `sz` bytes (`0 < sz`, fixed by `NewWriterSize`) over `wi`
(`io.streamWriterOk wi J Q Ew`, held); `sent` has gone to the underlying writer (`J sent`, held), `pend`
is buffered, not sent (`pend.length ≤ sz`); `□ Q (sent ++ pend)` (what the buffer will send is
allowed); `err` is the writer's sticky error (`nil` while healthy, else with `Ew`'s evidence; once
not `nil`, every later `Write`, `WriteByte` and `Flush` returns it and sends nothing). Clients
reason about `J sent` through `bufio.ownBufWriter_fact`.
Lean-first.
-/
module

public import Proof.bufio.Base
public import Proof.bufio.PkgInit
public import Proof.io.StreamWriterOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- Every read of `0 < m ≤ n` bytes, from any state `S r` of the stream, meets `Pre`
(persistent): what a buffer of `n` bytes needs of the reader it fills from. -/
def bufio.preUpTo (S : List w8 → IProp GF) (Pre : List w8 → Nat → Prop) (n : Nat) : IProp GF :=
  iprop(□ ∀ r, S r -∗ ⌜∀ m, 0 < m → m ≤ n → Pre r m⌝)

instance bufio.preUpTo_persistent (S : List w8 → IProp GF) (Pre : List w8 → Nat → Prop)
    (n : Nat) : Persistent (bufio.preUpTo S Pre n) := by
  unfold bufio.preUpTo; infer_instance

/-- A condition that holds of every read, at any state. -/
theorem bufio.preUpTo_of_pure (S : List w8 → IProp GF) (Pre : List w8 → Nat → Prop) (n : Nat)
    (h : ∀ r m, 0 < m → m ≤ n → Pre r m) : ⊢ bufio.preUpTo S Pre n := by
  unfold bufio.preUpTo
  iintro !> %r -
  ipureintro; exact h r

/-- Reads of a non-empty buffer (a connection's condition, `net.conn_readerOk`). -/
theorem bufio.preUpTo_trivial (S : List w8 → IProp GF) (n : Nat) :
    ⊢ bufio.preUpTo S (fun _ m => 0 < m) n :=
  bufio.preUpTo_of_pure S _ n (fun _ _ h _ => h)

/-- The condition at a state the stream is in. -/
theorem bufio.preUpTo_at (S : List w8 → IProp GF) (Pre : List w8 → Nat → Prop) (n : Nat)
    (r : List w8) :
    bufio.preUpTo S Pre n ⊢ S r -∗ S r ∗ ⌜∀ m, 0 < m → m ≤ n → Pre r m⌝ := by
  unfold bufio.preUpTo
  iintro #H HS
  ihave %h := H $$ HS
  iframe HS
  ipureintro; exact h

theorem bufio.preUpTo_eq {S : List w8 → IProp GF} {Pre : List w8 → Nat → Prop} {n n' : Nat}
    (h : n = n') : bufio.preUpTo S Pre n ⊢ bufio.preUpTo S Pre n' := by
  subst h; exact .rfl

/-- The evidence of a `*bufio.Reader`'s errors over a reader with the evidence `E`: `E`'s, or
the error is `io.ErrNoProgress`'s value. -/
def bufio.errE (E : List w8 → GoInterface → IProp GF) : List w8 → GoInterface → IProp GF :=
  fun r e => iprop(E r e ∨ globalAddr _root_.Perennial.io.ErrNoProgress ↦□ e)

/-- The fields of the `*bufio.Reader` `br` over `ri` buffering `pend` after returning `R`, with
the pending error `perr`: its buffer `buf` (`len(buf) > 0`, `szOk len(buf)`, every read of at most
its size from a state of `S` meets `Pre`) holding `pend` at `[r, w)`; `perr` with the evidence
`Eb` at `R ++ pend`. -/
def bufio.readerRep (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (Eb : List w8 → GoInterface → IProp GF) (szOk : Nat → Prop)
    (R pend : List w8) (perr : GoInterface) : IProp GF :=
  iprop(∃ (buf : GoSlice) (r w lb lrs : w64) (pre post : List w8),
    br ↦ _root_.Perennial.bufio.Reader.mk buf (interface.ok ri) r w perr lb lrs ∗
    buf ↦* (pre ++ pend ++ post) ∗
    ⌜sint.Z r = pre.length ∧ sint.Z w = pre.length + pend.length ∧
      0 < (pre ++ pend ++ post).length ∧ szOk (pre ++ pend ++ post).length ∧
      _root_.Perennial.io.ptrTyped perr⌝ ∗
    bufio.preUpTo S Pre (pre ++ pend ++ post).length ∗
    _root_.Perennial.io.errAt Eb (R ++ pend) perr)

/-- See the file header. -/
def bufio.ownBufReaderE (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (E Eb : List w8 → GoInterface → IProp GF) (szOk : Nat → Prop)
    (R : List w8) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ _root_.Perennial.io.readerOk ri Pre S E ∗
    ∃ (pend : List w8) (perr : GoInterface), S (R ++ pend) ∗
      bufio.readerRep br ri Pre S Eb szOk R pend perr)

/-- See the file header. -/
def bufio.ownBufReader (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF) (R : List w8) : IProp GF :=
  bufio.ownBufReaderE br ri Pre S E (bufio.errE E) (fun _ => True) R

/-- **A fact of the stream state inside a reader** (review R2): a persistent fact `Φ` that every
state `S r` gives and that holds of prefixes holds of what the reader has returned. (For a
connection: `net.connReader_proto`, the protocol fact of the bytes read.) -/
theorem bufio.ownBufReaderE_fact (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (E Eb : List w8 → GoInterface → IProp GF) (szOk : Nat → Prop)
    (R : List w8) (Φ : List w8 → IProp GF) [hΦ : ∀ r, Persistent (Φ r)]
    (hS : ∀ r, S r ⊢ S r ∗ Φ r) (hpre : ∀ x y, Φ (x ++ y) ⊢ Φ x) :
    bufio.ownBufReaderE br ri Pre S E Eb szOk R ⊢
      bufio.ownBufReaderE br ri Pre S E Eb szOk R ∗ Φ R := by
  unfold bufio.ownBufReaderE
  iintro ⟨#Hpkg, #Hrd, %pend, %perr, HS, Hrep⟩
  ihave ⟨HS, #HΦ⟩ := hS (R ++ pend) $$ HS
  ihave #HΦR := hpre R pend $$ HΦ
  iframe HΦR Hpkg Hrd
  iexists pend, perr
  iframe HS Hrep

/-- See `bufio.ownBufReaderE_fact`. -/
theorem bufio.ownBufReader_fact (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF) (R : List w8)
    (Φ : List w8 → IProp GF) [hΦ : ∀ r, Persistent (Φ r)]
    (hS : ∀ r, S r ⊢ S r ∗ Φ r) (hpre : ∀ x y, Φ (x ++ y) ⊢ Φ x) :
    bufio.ownBufReader br ri Pre S E R ⊢ bufio.ownBufReader br ri Pre S E R ∗ Φ R :=
  bufio.ownBufReaderE_fact br ri Pre S E _ _ R Φ hS hpre

/-- The size of the buffer `NewWriterSize(wr, size)` makes: `size`, or 4096 if `size ≤ 0`
(`bufio.go`: `if size <= 0 { size = defaultBufSize }`). -/
def bufio.writerSize (size : w64) : Nat :=
  if sint.Z size ≤ 0 then 4096 else (sint.Z size).toNat

/-- The fields of the `*bufio.Writer` `bw` over `wi` buffering `pend`, with the sticky error
`err`: its buffer `buf` of `sz` bytes (`0 < sz`) holding `pend` at `[0, n)`. -/
def bufio.writerRep (bw : Loc) (wi : GoInterfaceOk) (Ew : GoInterface → IProp GF) (sz : Nat)
    (pend : List w8) (err : GoInterface) : IProp GF :=
  iprop(∃ (buf : GoSlice) (n : w64) (rest : List w8),
    bw ↦ _root_.Perennial.bufio.Writer.mk err buf n (interface.ok wi) ∗ buf ↦* (pend ++ rest) ∗
    ⌜sint.Z n = pend.length ∧ 0 < (pend ++ rest).length ∧ (pend ++ rest).length = sz⌝ ∗
    io.werrAt Ew err)

/-- See the file header. -/
def bufio.ownBufWriter (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF)
    (Ew : GoInterface → IProp GF) (sz : Nat) (sent pend : List w8) (err : GoInterface) :
    IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ io.streamWriterOk wi J Q Ew ∗ J sent ∗
    □ Q (sent ++ pend) ∗ bufio.writerRep bw wi Ew sz pend err)

/-- **A fact of the sent bytes' state** (review W4): a persistent fact `Ψ` that the writer's
state `J w` gives holds of what has been sent. (For a connection, `sendTok_sentLb`: the bytes
sent so far, `sentLb`.) -/
theorem bufio.ownBufWriter_fact (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF)
    (Ew : GoInterface → IProp GF) (sz : Nat) (sent pend : List w8) (err : GoInterface)
    (Ψ : List w8 → IProp GF) [hΨ : ∀ w, Persistent (Ψ w)] (hJ : ∀ w, J w ⊢ J w ∗ Ψ w) :
    bufio.ownBufWriter bw wi J Q Ew sz sent pend err ⊢
      bufio.ownBufWriter bw wi J Q Ew sz sent pend err ∗ Ψ sent := by
  unfold bufio.ownBufWriter
  iintro ⟨#Hpkg, #Hwr, HJ, #HQ, Hrep⟩
  ihave ⟨HJ, #HΨ⟩ := hJ sent $$ HJ
  iframe HΨ Hpkg Hwr HJ HQ Hrep

/-- A permission needed only when `φ` holds, as a persistent one (review W1: `Write`'s and
`WriteByte`'s `⌜err = nil⌝ -∗ □ Q …`). -/
theorem bufio.wand_pure_persistent (φ : Prop) (P : IProp GF) :
    (⌜φ⌝ -∗ □ P) ⊢ □ (∀ _ : φ, P) := by
  by_cases h : φ
  · iintro H
    ihave #HP := H $$ %h
    imodintro
    iintro %_
    iexact HP
  · iintro -
    imodintro
    iintro %h'
    exact absurd h' h

/-- A writer buffers at most its size, and its size is positive. -/
theorem bufio.ownBufWriter_size (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF)
    (Ew : GoInterface → IProp GF) (sz : Nat) (sent pend : List w8) (err : GoInterface) :
    bufio.ownBufWriter bw wi J Q Ew sz sent pend err ⊢
      ⌜pend.length ≤ sz ∧ 0 < sz⌝ ∗ bufio.ownBufWriter bw wi J Q Ew sz sent pend err := by
  unfold bufio.ownBufWriter bufio.writerRep
  iintro ⟨#Hpkg, #Hwr, HJ, #HQ, %buf, %n, %rest, Hb, Hbuf, %Hn, #Herr⟩
  isplitr
  · ipureintro
    obtain ⟨-, h1, h2⟩ := Hn
    simp only [List.length_append] at h1 h2 ⊢
    omega
  iframe Hpkg Hwr HJ HQ
  iexists buf, n, rest
  iframe Hb Hbuf Herr
  ipureintro; exact Hn

/-- A writer's sticky error has its evidence. -/
theorem bufio.ownBufWriter_err (bw : Loc) (wi : GoInterfaceOk) (J Q : List w8 → IProp GF)
    (Ew : GoInterface → IProp GF) (sz : Nat) (sent pend : List w8) (err : GoInterface) :
    bufio.ownBufWriter bw wi J Q Ew sz sent pend err ⊢ io.werrAt Ew err := by
  unfold bufio.ownBufWriter bufio.writerRep
  iintro ⟨-, -, -, -, %buf, %n, %rest, -, -, -, #H⟩
  iexact H

/-- `bufio` initialized `io`. -/
theorem bufio.io_init_of_bufio :
    isPkgInit (PROP := IProp GF) pkg_id.bufio ⊢ isPkgInit (PROP := IProp GF) pkg_id.io := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.bufio).trans ?_
  show iprop(isPkgInit pkg_id.bytes ∗ isPkgInit pkg_id.errors ∗ isPkgInit pkg_id.io ∗
    isPkgInit pkg_id.strings ∗ True) ⊢ _
  iintro ⟨-, -, H, -⟩
  iexact H

/-- `io.ErrNoProgress` holds a non-`nil` pointer error. -/
theorem bufio.errNoProgress_init [_root_.Perennial.io.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢
      ∃ e : GoInterface, globalAddr _root_.Perennial.io.ErrNoProgress ↦□ e ∗
        ⌜_root_.Perennial.io.ptrTyped e ∧ e ≠ interface.nil⌝ := by
  iintro #Hio
  ihave #Hi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, -, -, #HNP, -⟩
  iunfold _root_.Perennial.errors.newVar at HNP
  icases HNP with ⟨%x, #Hx, -⟩
  iexists _
  iframe Hx
  ipureintro
  refine ⟨?_, by simp⟩
  intro ii T h _
  cases h
  exact ⟨x, rfl⟩

/-- An error of the underlying reader, as one of the buffered reader's. -/
theorem bufio.errAt_errE (E : List w8 → GoInterface → IProp GF) (r : List w8) (e : GoInterface) :
    _root_.Perennial.io.errAt E r e ⊢ _root_.Perennial.io.errAt (bufio.errE E) r e := by
  unfold _root_.Perennial.io.errAt bufio.errE
  iintro (%h | #H)
  · ileft; ipureintro; exact h
  · iright; imodintro; ileft; iexact H

/-- An error with the evidence `E`, with a weaker evidence. -/
theorem bufio.errAt_weaken (E Eb : List w8 → GoInterface → IProp GF) (r : List w8)
    (e : GoInterface) :
    (□ ∀ r e, E r e -∗ Eb r e) ⊢ _root_.Perennial.io.errAt E r e -∗
      _root_.Perennial.io.errAt Eb r e := by
  unfold _root_.Perennial.io.errAt
  iintro #HEb (%h | #H)
  · ileft; ipureintro; exact h
  · iright; imodintro; iapply HEb $$ H

/-- `E`'s evidence is `bufio.errE E`'s. -/
theorem bufio.errE_weaken (E : List w8 → GoInterface → IProp GF) :
    ⊢ □ ∀ r e, E r e -∗ bufio.errE E r e := by
  iintro !> %r %e H
  unfold bufio.errE
  ileft; iexact H

theorem bufio.errAt_nil' (E : List w8 → GoInterface → IProp GF) (r : List w8) :
    ⊢ _root_.Perennial.io.errAt E r interface.nil := by
  unfold _root_.Perennial.io.errAt
  ileft; ipureintro; rfl

end defs

section pure2

/-- A `w64` whose signed value is a natural number `k` is `W64 k`. -/
theorem bufio.w64_of_sintZ {n : w64} {k : Nat} (h : sint.Z n = k) : n = W64 k := by
  apply BitVec.eq_of_toInt_eq
  rw [show BitVec.toInt n = sint.Z n from rfl, h]
  have hk : k < 2 ^ 63 := by
    have : sint.Z n < 2 ^ 63 := by word
    omega
  exact (bufio.sint_Z_W64_length hk).symm

end pure2

end EtcdGrove
end Perennial
