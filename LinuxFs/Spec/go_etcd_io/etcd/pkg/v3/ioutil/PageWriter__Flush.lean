/-
`pw.Flush()` (pagewriter.go): `flush`'s spec without the count: hands the buffered bytes `pend` to
the writer `wi` in one `Write` (none if `pend` is empty) and drops the buffer whatever it returns: on
success the writer has all of `pend`; on an error it is broken (`B out pend`, `io.writerStream`). Proved in `LinuxFs/Proof/go_etcd_io/etcd/pkg/v3/ioutil/PageWriter__Flush.lean`.
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
abbrev go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.Flush.spec : Prop :=
  ∀ (pw : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF) (B : List w8 → List w8 → IProp GF)
    (out pend : List w8),
  ⊢ io.writerStream wi W B -∗
    {{ ioutil.ownPageWriter pw wi pend ∗ W out }}
      (App (Val (pw @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.ty @!!
        go!"Flush")) (Val #()))
    {{ (err : GoInterface), RET #err;
        ioutil.ownPageWriter pw wi [] ∗
        ((⌜err = GoInterface.nil⌝ ∗ W (out ++ pend)) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ B out pend)) }}

end spec

end EtcdGrove
end Perennial
