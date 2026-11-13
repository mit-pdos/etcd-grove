/-
`pw.flush()` (pagewriter.go, private): hands the buffered bytes `pend` to the writer `wi` in one
`Write` (none if `pend` is empty) and drops the buffer whatever it returns: on an error, the writer
has a prefix `ys` of `pend` (what `io.writerStream` allows) and the rest is lost. Returns the
writer's count. Proved in `LinuxFs/Proof/go_etcd_io/etcd/pkg/v3/ioutil/PageWriter__flush.lean`.
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
  ∀ (pw : Loc) (wi : GoInterfaceOk) (W : List w8 → IProp GF) (out pend : List w8),
  ⊢ io.writerStream wi W -∗
    {{ ioutil.ownPageWriter pw wi pend ∗ W out }}
      (App (Val (pw @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.ioutil.PageWriter.ty @!!
        go!"flush")) (Val #()))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, ⌜ys <+: pend ∧ sint.Z n = ys.length ∧ (err = GoInterface.nil → ys = pend)⌝ ∗
        W (out ++ ys) ∗ ioutil.ownPageWriter pw wi [] }}

end spec

end EtcdGrove
end Perennial
