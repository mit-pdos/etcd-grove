/-
`f.ReadAt(b, off)` on an open `*os.File` (this repository's `os`, project `bboltfs`), reading
bytes inside the file that the client holds (any fractions), with a fraction of the file's
`OsMeta` (so that the size is known): a non-negative offset, `b` of at most `maxRW` (1 GiB)
bytes, and `off + len(b)` at most the size. The model (`TrustedCode/os.lean`) makes one `pread`
(the extension's `PRead`, `wp_PRead`) per iteration, retried on `EINTR`. On success `b` holds the
bytes and the result is `(len(b), nil)`; on failure, `(0, err)` with a non-nil `err`, and `b` holds
anything. Proved in `Proof/os/File__ReadAt.lean`. Lean-first (no Rocq counterpart). `specRacy`, below, is the racing read.
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.File.ReadAt.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (vs : List w8)
    (off : w64) (dq dqm dqb : DFrac) (d : OsFd) (m : OsMeta) (xs : List (w8 × Bool)),
  d.readable = true → 0 ≤ off.toInt → vs.length ≤ 0x40000000 →
  off.toNat + vs.length ≤ m.size → xs.length = vs.length →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦* vs ∗
      osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.path dqm (some m) ∗
      osBytes (GF := GF) d.path off.toNat dqb xs }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"ReadAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ osFd fd dq d ∗ osMeta d.path dqm (some m) ∗
      osBytes d.path off.toNat dqb xs ∗
      ∃ vs' : List w8, sl ↦* vs' ∗
        ⌜vs'.length = vs.length ∧
          ((n = W64 vs.length ∧ err = interface.nil ∧ vs' = xs.map Prod.fst) ∨
           (n = W64 0 ∧ err ≠ interface.nil))⌝ }}

/-- A racing `f.ReadAt(b, off)` (minibolt's `Snapshot`, which reads while the writer may write
past what it knows, or a meta page it does not hold): no `OsMeta`, and bytes of the file held at
any fractions, in ranges `rs` (each `(off, dq, xs)`: `osBytes path off dq xs`). The model makes
one `pread` (`wp_PRead_racy`) per iteration, retried on `EINTR`, until `b` is full, a `pread`
reads nothing (`io.EOF`, whose value `eof` the client knows) or one fails. The result's `n`
bytes of `b` are exact at every held byte; with `nil` they are all of `b`, and with `io.EOF`
they reach every held byte inside `[off, off + len(b))`. A failure is a `*PathError`, so never
`io.EOF`. Past `n`, `b` holds anything. -/
abbrev os.File.ReadAt.specRacy : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (vs : List w8)
    (off : w64) (dq : DFrac) (d : OsFd) (rs : List (Nat × DFrac × List (w8 × Bool)))
    (eof : GoInterface),
  d.readable = true → 0 ≤ off.toInt → vs.length ≤ 0x40000000 →
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ sl ↦* vs ∗
      osFd (GF := GF) fd dq d ∗
      ([∗list] r ∈ rs, osBytes (GF := GF) d.path r.1 r.2.1 r.2.2) ∗
      globalAddr io.EOF ↦□ eof }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"ReadAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ([∗list] r ∈ rs, osBytes d.path r.1 r.2.1 r.2.2) ∗
      ∃ vs' : List w8, sl ↦* vs' ∗
        ⌜vs'.length = vs.length ∧ n.toNat ≤ vs.length ∧
          (∀ i b, os.heldByte rs i b → off.toNat ≤ i → i < off.toNat + n.toNat →
            vs'[i - off.toNat]? = some b) ∧
          ((err = interface.nil ∧ n.toNat = vs.length) ∨
           (err = eof ∧ ∀ i b, os.heldByte rs i b → off.toNat ≤ i →
              i < off.toNat + vs.length → i < off.toNat + n.toNat) ∨
           (∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe))⌝ }}

end spec

end EtcdGrove
end Perennial
