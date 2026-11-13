/-
`pw.flush()` (pagewriter.go, private): hands the buffered bytes `pend` to the writer `wi` in one
`Write` (none if `pend` is empty) and drops the buffer whatever it returns: on success the writer has
all of `pend` and the count is `len(pend)`; on an error the writer is broken (`B out pend`, what
`io.writerStream` gives of a failed write) and the count is the writer's, any. Proved in `LinuxFs/Proof/go_etcd_io/etcd/pkg/v3/ioutil/PageWriter__flush.lean`.
WAL W6, 2026-11-13; Lean-first.
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
abbrev go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.flush.spec : Prop :=
  ∀ (pw : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF)
    (lim : Nat) (out pend : List w8),
  out.length + pend.length ≤ lim →
  ⊢ io.writerStream wi lim W B -∗
    {{ ioutil.ownPageWriter pw wi pend ∗ W out }}
      (App (Val (pw @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.ty @!!
        go!"flush")) (Val #()))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ioutil.ownPageWriter pw wi [] ∗
        ((⌜err = GoInterface.nil ∧ sint.Z n = pend.length⌝ ∗ W (out ++ pend)) ∨
         (⌜err ≠ GoInterface.nil⌝ ∗ B out pend)) }}

end spec

end EtcdGrove
end Perennial
