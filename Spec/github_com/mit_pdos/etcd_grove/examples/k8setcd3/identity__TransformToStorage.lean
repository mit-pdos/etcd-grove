/- Lean-first (no Rocq counterpart).

`identity{}.TransformToStorage(ctx, data, dataCtx)` (k8setcd3.go): the data.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

/-- See the file header. -/
abbrev identity.TransformToStorage.spec : Prop :=
  ∀ (ctx : GoInterface) (sl : GoSlice) (dctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 }}
    (App (App (App (Val #(methods github_com.mit_pdos.etcd_grove.examples.k8setcd3.identity.ty go!"TransformToStorage" #(github_com.mit_pdos.etcd_grove.examples.k8setcd3.identity.mk))) (Val #ctx)) (Val #sl))
      (Val #dctx))
  {{ RET (PairV #sl #GoInterface.nil); True }}

end spec

end k8setcd3
end EtcdGrove
end Perennial
