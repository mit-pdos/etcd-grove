/-
`flock(db, exclusive, timeout)` (`bolt_unix.go`): `Flock` (trivial in OsFs), retried until the timeout.
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

/-- (internal) locked, or an error. -/
def flock.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM) (ex : Bool) (to : w64),
  {{ dbRaw (GF := GF) db γ M }}
    (App (App (App (Val (@! go_etcd_io.bbolt.flock)) (Val #db)) (Val #ex)) (Val #to))
  {{ (err : GoInterface), RET #err; dbRaw db γ M }}

end spec

end Bbolt
end EtcdGrove
end Perennial
