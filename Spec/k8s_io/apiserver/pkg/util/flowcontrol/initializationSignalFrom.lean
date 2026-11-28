/-
`initializationSignalFrom(ctx)` (`k8s.io/apiserver/pkg/util/flowcontrol/apf_context.go:42-45`): of a
context whose value at APF's initialization-signal key is nil or not an `InitializationSignal`
(`flowcontrol.initSignalRes`, k8s 7f-5 T5-b), answers no signal (`ok = false`). Proved (k8s 7f-5a-P
step 3). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.audit.CtxKeys
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev flowcontrol.initializationSignalFrom.spec : Prop :=
  ∀ (ci : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.util.flowcontrol ∗
      context.valueAt ci flowcontrol.initSignalKeyAny (flowcontrol.initSignalRes (hG := hG)) }}
    (App (Val (@! k8s_io.apiserver.pkg.util.flowcontrol.initializationSignalFrom))
      (Val #(GoInterface.ok ci)))
  {{ (s : GoInterface) (ok : Bool), RET (PairV #s #ok); ⌜ok = false⌝ }}

end spec

end EtcdGrove
end Perennial
