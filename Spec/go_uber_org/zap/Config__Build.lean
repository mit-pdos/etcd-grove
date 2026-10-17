/-
`(*zap.Config).Build(opts...)` (`go.uber.org/zap`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open go_etcd_io.etcd.cache.v3 (errorStringSpec)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `lc.Build()` (no options) returns a non-nil logger and no error, or an error whose `Error()`
returns some string. It reads the caller's `*zap.Config` (opaque here, `zap` names only). -/
abbrev zap.Config.Build.spec : Prop :=
  ∀ (lc : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (Val (lc @!! go.GoType.PointerType go_uber_org.zap.Config.ty @!! go!"Build"))
      (Val #slice.nil))
  {{ (lg : Loc) (err : GoInterface), RET (PairV #lg #err);
      ((⌜err = GoInterface.nil⌝ ∗ ⌜lg ≠ null⌝) ∨
        ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errorStringSpec e) }}

end spec

end EtcdGrove
end Perennial
