/- Lean-first (no Rocq counterpart).

`versioner{}.ParseResourceVersion(s)` (k8setcd3.go): `parseRV(s)`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev versioner.ParseResourceVersion.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 }}
    (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner.ty go!"ParseResourceVersion" #(github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner.mk))) (Val #s))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      match parseRVD s with
      | some m => ⌜err = GoInterface.nil ∧ n = m⌝
      | none => ⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
