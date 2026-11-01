/-
`f.ReadAt(b, off)` on an open `*os.File` (this repository's `os`, project `bboltfs`), reading
bytes inside the file that the client holds (any fractions), with a fraction of the file's
`OsMeta` (so that the size is known): a non-negative offset, `b` of at most `maxRW` (1 GiB)
bytes, and `off + len(b)` at most the size. The model (`TrustedCode/os.lean`) makes one `pread`
(the extension's `PRead`, `wp_PRead`) per iteration, retried on `EINTR`. On success `b` holds the
bytes and the result is `(len(b), nil)`; on failure, `(0, err)` with a non-nil `err`, and `b` holds
anything. Proved in `Proof/os/File__ReadAt.lean`. Lean-first (no Rocq counterpart).
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

end spec

end EtcdGrove
end Perennial
