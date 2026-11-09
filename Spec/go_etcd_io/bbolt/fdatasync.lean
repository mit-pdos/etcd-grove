/-
`fdatasync(db)` (`bolt_linux.go`): `syscall.Fdatasync` of the file's fd (OsFs's `Fdatasync`).
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

/-- (internal) the file synced, or an error (D2: the dirty bytes lost). -/
def fdatasync.spec : Prop :=
  ∀ [HasExt osFsExt] (db : Loc) (γ : BoltName) (M : DbM),
  {{ dbRaw (GF := GF) db γ M }}
    (App (Val (@! go_etcd_io.bbolt.fdatasync)) (Val #db))
  {{ (err : GoInterface), RET #err; dbRaw db γ M }}

end spec

end Bbolt
end EtcdGrove
end Perennial
