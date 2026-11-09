/-
`newFreelist(t)` (`db.go`): the hash map freelist for `FreelistMapType`, else the array one (4d's constructors).
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

/-- (internal) an empty freelist with no readers. -/
def newFreelist.spec : Prop :=
  ∀ [HasExt osFsExt] (t : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt }}
    (App (Val (@! go_etcd_io.bbolt.newFreelist)) (Val t))
  {{ (fl : GoInterface), RET #fl; ⌜fl ≠ GoInterface.nil⌝ }}

end spec

end Bbolt
end EtcdGrove
end Perennial
