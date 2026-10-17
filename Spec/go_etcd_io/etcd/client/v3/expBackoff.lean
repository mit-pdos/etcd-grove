/-
`expBackoff(generation, exponent, minDelay, maxDelay)` (`client/v3/utils.go`; new in PR
etcd#20731): `time.Duration(math.Min(math.Pow(exponent, float64(generation))*float64(minDelay),
float64(maxDelay)))`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (backoffOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `expBackoff(g, e, lo, hi)` returns some duration. Only that it returns (no panic) is stated:
`math.Pow` and `math.Min` have no specs, float arithmetic is uninterpreted and the conversion of a
`float64` to `time.Duration` has no semantics in Perennial. Its value (`min(e^g * lo, hi)`, and
what it is when that is at least 2^63 ns) is checked by Go tests instead
(`notes/pr-verify/etcd-20731/`). -/
abbrev expBackoff.spec : Prop :=
  ∀ (g e lo hi : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.expBackoff)) (Val #g)) (Val #e))
      (Val #lo)) (Val #hi))
  {{ (r : w64), RET #r; True }}

end spec

end EtcdGrove
end Perennial
