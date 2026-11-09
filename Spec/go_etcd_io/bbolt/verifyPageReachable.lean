/-
`verifyPageReachable(...)` (`tx_check.go`): reports a page past the high-water mark, reached twice, or freed.
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) returns; nothing reported on a well-formed tree. -/
def verifyPageReachable.spec : Prop :=
  ∀ [HasExt osFsExt] (a1 a2 a3 a4 a5 a6 : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.bbolt.verifyPageReachable)) (Val a1)) (Val a2)) (Val a3)) (Val a4)) (Val a5)) (Val a6))
  {{ RET #(); True }}

end spec

end Bbolt
end EtcdGrove
end Perennial
