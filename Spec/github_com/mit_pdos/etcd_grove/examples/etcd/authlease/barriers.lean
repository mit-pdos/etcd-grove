/-
`barriers(ms, lg)` (`examples/etcd/authlease/authlease.go`; auth-lease S4, item 9): `barrier` at every
member of `ms`, in order, stopping at the first that fails. Lean-first (no Rocq counterpart).

**The triple:** for each member, `barrier.spec`'s arguments (`BArgs`, their client addresses the
members') and precondition (`barrierPre`): `true` gives `barrier`'s success at every member
(`barrierPost`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Env

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

/-- See the file header. -/
abbrev barriers.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (msl : GoSlice) (lg : Loc) (ms : List etcdstart.GMember) (bs : List (BArgs GF)),
  ms.map (·.Client') = bs.map (·.addr) → threadBound GF ≤ 2 ^ 30 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authlease ∗
      zapLoggerOk lg ∗ msl ↦*□ ms ∗ [∗list] b ∈ bs, barrierPre b }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.authlease.barriers)) (Val #msl))
      (Val #lg))
  {{ (ok : Bool), RET #ok; ⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ [∗list] b ∈ bs, barrierPost b) }}

end spec

end etcd_authlease
end EtcdGrove
end Perennial
