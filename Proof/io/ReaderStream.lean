/-
**An `io.Reader` read as a stream** (WAL leaf specs, 2026-11-13): the vocabulary of the specs of
`io.ReadFull` (`Spec/io/ReadFull.lean`), `binary.Read` of an `*int64` (`Spec/encoding/binary/
ReadInt64LE.lean`) and `*bufio.Reader`'s `Read` (`LinuxFs/Spec/bufio/Reader__Read.lean`), which
the WAL's decoder composes (decoder.go: `readInt64`, `io.ReadFull(fileBufReader, data)`).

* `io.readerStream ri S E` (persistent): `ri.Read(p)`, from the state `S r` (`r` the bytes it has
  delivered so far), delivers the next `n` bytes `ys` into the front of `p` (`0 ≤ n ≤ len(p)`,
  `io.Reader`'s contract), leaves `S (r ++ ys)`, and returns `nil` or an error with the evidence
  `E (r ++ ys)` gives of it (`io.errAt`, persistent). The client chooses `S` (what the bytes are: a
  file's content from an offset, ...) and `E` (what an error says there: `io.EOF` only at the end,
  ...). `E` is an Iris predicate (2026-11-14, ledger "the readers' errors and `errors.Is`"): an
  error's identity under `errors.Is` is a heap fact (a `*PathError`'s `Err` field), which a pure
  predicate cannot carry. The caller keeps the end of the read below
  `2^62` (`len(r) + len(p) < 2^62`): the `*os.File` model does not model a read ending past
  `model.offMax`, and no reader here gets near it (`notes/wal-fsext-plan.md`, W3/W5 log, `wal-read5`).
* `io.readFullRes E eof ueof r ys m err`: what `io.ReadFull` of `m` bytes returns after delivering
  `ys` from `r` on: all `m` and `nil`, or fewer and the reader's last error `e` (with its evidence
  `E (r ++ ys) e`), but `io.ErrUnexpectedEOF` in place of `io.EOF` when some bytes came first (io.go,
  `ReadAtLeast`). `io.readFullOk P ...` is its pure shadow for a pure consequence `P` of `E`
  (`io.readFullRes_pure`).
Lean-first.
-/
module

public import Perennial.Proof.io

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `err` is `nil` or an error with the evidence `E r err` (persistently). -/
def io.errAt (E : List w8 → GoInterface → IProp GF) (r : List w8) (err : GoInterface) : IProp GF :=
  iprop(⌜err = GoInterface.nil⌝ ∨ □ E r err)

instance io.errAt_persistent (E : List w8 → GoInterface → IProp GF) (r : List w8)
    (err : GoInterface) : Persistent (io.errAt E r err) := by
  unfold io.errAt; infer_instance

theorem io.errAt_nil (E : List w8 → GoInterface → IProp GF) (r : List w8) :
    ⊢ io.errAt E r GoInterface.nil := by
  unfold io.errAt; ileft; ipureintro; rfl

theorem io.errAt_eq {E : List w8 → GoInterface → IProp GF} {r r' : List w8} {err : GoInterface}
    (h : r = r') : io.errAt E r err ⊢ io.errAt E r' err := by
  subst h; exact .rfl

/-- See the file header. -/
def io.readerStream (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) : IProp GF :=
  iprop(□ ∀ (r : List w8) (p : GoSlice) (xs : List w8),
    {{ ⌜r.length + xs.length < 2 ^ 62⌝ ∗ S r ∗ p ↦* xs }}
      (App (Val #(methods ri.ty go!"Read" ri.v)) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
          io.errAt E (r ++ ys) err ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ S (r ++ ys) }})

instance io.readerStream_persistent (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) : Persistent (io.readerStream ri S E) := by
  unfold io.readerStream; infer_instance

/-- See the file header. -/
def io.readFullRes (E : List w8 → GoInterface → IProp GF) (eof ueof : GoInterface)
    (r ys : List w8) (m : Nat) (err : GoInterface) : IProp GF :=
  iprop(⌜ys.length = m ∧ err = GoInterface.nil⌝ ∨
    ∃ e : GoInterface, ⌜ys.length < m ∧ e ≠ GoInterface.nil ∧
      (e = eof ∧ ys ≠ [] → err = ueof) ∧ (¬ (e = eof ∧ ys ≠ []) → err = e)⌝ ∗ □ E (r ++ ys) e)

instance io.readFullRes_persistent (E : List w8 → GoInterface → IProp GF) (eof ueof : GoInterface)
    (r ys : List w8) (m : Nat) (err : GoInterface) :
    Persistent (io.readFullRes E eof ueof r ys m err) := by
  unfold io.readFullRes; infer_instance

end defs

section pure
variable [GooseExts]

/-- See the file header (`io.readFullRes`'s pure shadow). -/
def io.readFullOk (E : List w8 → GoInterface → Prop) (eof ueof : GoInterface) (r ys : List w8)
    (m : Nat) (err : GoInterface) : Prop :=
  (ys.length = m ∧ err = GoInterface.nil) ∨
  (ys.length < m ∧ ∃ e, e ≠ GoInterface.nil ∧ E (r ++ ys) e ∧
    (e = eof ∧ ys ≠ [] → err = ueof) ∧ (¬ (e = eof ∧ ys ≠ []) → err = e))

/-- A failed `ReadFull` returns a non-`nil` error, if `io.ErrUnexpectedEOF` is not `nil`. -/
theorem io.readFullOk_err_ne_nil {E : List w8 → GoInterface → Prop} {eof ueof : GoInterface}
    {r ys : List w8} {m : Nat} {err : GoInterface} (hu : ueof ≠ GoInterface.nil)
    (h : io.readFullOk E eof ueof r ys m err) (hlt : ys.length < m) : err ≠ GoInterface.nil := by
  rcases h with ⟨hl, _⟩ | ⟨_, e, he, _, h1, h2⟩
  · omega
  · by_cases hc : e = eof ∧ ys ≠ []
    · rw [h1 hc]; exact hu
    · rw [h2 hc]; exact he

end pure

section shadow
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `io.readFullRes`'s pure shadow, for a pure consequence `P` of the evidence. -/
theorem io.readFullRes_pure {E : List w8 → GoInterface → IProp GF} {P : List w8 → GoInterface → Prop}
    {eof ueof : GoInterface} {r ys : List w8} {m : Nat} {err : GoInterface}
    (hP : ∀ r e, E r e ⊢ ⌜P r e⌝) :
    io.readFullRes E eof ueof r ys m err ⊢ ⌜io.readFullOk P eof ueof r ys m err⌝ := by
  unfold io.readFullRes
  iintro (%h | ⟨%e, %h, #HE⟩)
  · ipureintro; exact Or.inl h
  · ihave %hp := (hP (r ++ ys) e) $$ HE
    ipureintro
    exact Or.inr ⟨h.1, e, h.2.1, hp, h.2.2⟩

end shadow

end EtcdGrove
end Perennial
