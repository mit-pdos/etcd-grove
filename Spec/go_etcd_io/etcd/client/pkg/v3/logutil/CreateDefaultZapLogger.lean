/-
`logutil.CreateDefaultZapLogger(level)` (`client/pkg/v3/logutil`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.go_etcd_io.etcd.client.v3.ErrOrigin

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

/-- `logutil.CreateDefaultZapLogger(level)` returns a non-nil logger and no error, or an error whose
`Error()` returns some string, marked `loggerErr` (`ErrOrigin.lean`, a ghost mark) (`DefaultZapLoggerConfig.Build()`'s). -/
abbrev logutil.CreateDefaultZapLogger.spec : Prop :=
  ∀ (lv : w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.logutil }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.logutil.CreateDefaultZapLogger)) (Val #lv))
  {{ (lg : Loc) (err : GoInterface), RET (PairV #lg #err);
      ((⌜err = GoInterface.nil⌝ ∗ ⌜lg ≠ null⌝) ∨
        ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errorStringSpec e ∗ ⌜loggerErr e⌝) }}

end spec

end EtcdGrove
end Perennial
