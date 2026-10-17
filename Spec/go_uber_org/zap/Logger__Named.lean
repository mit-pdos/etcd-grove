/-
`(*zap.Logger).Named(s)` (`go.uber.org/zap`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI


section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `lg.Named(s)` of a non-nil logger returns a non-nil logger (a clone with the name appended). -/
abbrev zap.Logger.Named.spec : Prop :=
  ∀ (lg : Loc) (s : GoString), lg ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap }}
    (App (Val (lg @!! go.GoType.PointerType go_uber_org.zap.Logger.ty @!! go!"Named")) (Val #s))
  {{ (l : Loc), RET #l; ⌜l ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
