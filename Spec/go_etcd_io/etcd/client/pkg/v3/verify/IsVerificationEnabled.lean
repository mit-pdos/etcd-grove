/-
`verify.IsVerificationEnabled(t)` (`client/pkg/verify/verify.go`): whether `ETCD_VERIFY` (lower-cased)
is `all` or `t` lower-cased. Lean-first (etcdstorage, 2026-11-20).
-/
module

public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.client.pkg.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.verify.Assumptions]

/-- `IsVerificationEnabled(t)` returns; with `ETCD_VERIFY` off for the run (`EtcdVerifyOff`), it
returns `false` for the checks etcd's code asks about, `assert` (`Verify`) and `lock` (the backend's
lock checks). -/
abbrev verify.IsVerificationEnabled.spec : Prop :=
  ∀ (t : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify }}
    (App (Val (@! verify.IsVerificationEnabled)) (Val #t))
  {{ (b : Bool), RET #b;
      ⌜EtcdVerifyOff → t = go!"assert" ∨ t = go!"lock" → b = false⌝ }}

end spec

end EtcdGrove
end Perennial
