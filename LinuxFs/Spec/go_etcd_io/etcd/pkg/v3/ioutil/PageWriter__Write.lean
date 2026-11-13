/-
`pw.Write(p)` (pagewriter.go): the page writer accepts all of `p`'s bytes `xs`: it buffers them, or
hands the buffer, the bytes completing its last page and then whole pages of `xs` to the writer `wi`,
buffering the rest. On success (`n = len(p)`) the writer's new bytes `ys` then the new buffer `pend'`
are the old buffer then `xs`. On an error (a `Write` of `wi` failed: the buffer's, or the whole
pages') the buffer is empty and the writer is broken by that `Write`: `B (out ++ a) b`
(`io.writerStream`), `a` the bytes it had accepted before, `b` the ones the failed `Write` was
given, `a ++ b` a prefix of the old buffer then `xs`; the rest is lost. `p` is only read, at any fraction; its length is below
`2^62` (`len(p) + bufferedBytes` must not overflow), and the writer's bytes, the buffer's and `p`'s
fit the writer's bound `lim`. Proved in
`LinuxFs/Proof/go_etcd_io/etcd/pkg/v3/ioutil/PageWriter__Write.lean`. WAL W6, 2026-11-13; Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.pkg.v3.ioutil.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.Write.spec : Prop :=
  ∀ (pw : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF)
    (lim : Nat) (out pend : List w8) (p : GoSlice) (xs : List w8) (dq : DFrac),
  xs.length < 2 ^ 62 → out.length + pend.length + xs.length ≤ lim →
  ⊢ io.writerStream wi lim W B -∗
    {{ ioutil.ownPageWriter pw wi pend ∗ W out ∗ p ↦*{dq} xs }}
      (App (Val (pw @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.ty @!!
        go!"Write")) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ pend' : List w8, ioutil.ownPageWriter pw wi pend' ∗ p ↦*{dq} xs ∗
        ((∃ ys : List w8, ⌜err = GoInterface.nil ∧ ys ++ pend' = pend ++ xs ∧ sint.Z n = xs.length⌝ ∗
            W (out ++ ys)) ∨
         (∃ a b : List w8, ⌜err ≠ GoInterface.nil ∧ pend' = [] ∧ a ++ b <+: pend ++ xs⌝ ∗
            B (out ++ a) b)) }}

end spec

end EtcdGrove
end Perennial
