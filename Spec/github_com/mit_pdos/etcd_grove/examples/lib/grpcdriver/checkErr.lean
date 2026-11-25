/- Lean-first (no Rocq counterpart).

`checkErr(err)`: the section error-set; it returns for an error that is a status or `io.EOF`
(`errOk`), and reports the section (`reached`, whose calls return: `drvFacts`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.PlainInvoke

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

/-- See the file header. -/
abbrev checkErr.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
      drvFacts ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
      (⌜go_etcd_io.etcd.cache.v3.hasGRPCStatus err⌝ ∨ eofIs err) }}
    (App (Val (@! checkErr)) (Val #err))
  {{ RET #(); True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
