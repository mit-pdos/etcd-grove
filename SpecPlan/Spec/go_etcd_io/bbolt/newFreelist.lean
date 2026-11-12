/-
`newFreelist(t)` (`db.go`): the hash map freelist for `FreelistMapType`, else the array one (4d's constructors).
(internal; mirrors the code. Round 1, review C8: a proved function of the old tree.)

**Proof sketch.** 4d's `NewHashMapFreelist.spec` or `NewArrayFreelist.spec` (bbolt's package
initialization gives the freelist package's), whose posts are this one's at `hashMapIface l` /
`arrayIface l`.

**Changes (integration I7).** The post was only `fl ≠ nil`: `loadFreelist` needs the freelist's
resources (4d's `flOwn`/`flReaders` of an empty freelist) to call `Init`/`Read`.
-/
module

public import SpecPlan.Spec.go_etcd_io.bbolt.Internal

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

/-- (internal) a new, empty freelist with no readers (4d's `flOwn fl FLState.empty`,
`flReaders fl []`), a `*hashMap` or a `*array`. -/
def newFreelist.spec : Prop :=
  ∀ [HasExt osFsExt] (t : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt }}
    (App (Val (@! go_etcd_io.bbolt.newFreelist)) (Val t))
  {{ (fl : GoInterface), RET #fl; ⌜fl ≠ GoInterface.nil⌝ ∗
      Freelist.flOwn fl Freelist.FLState.empty ∗ Freelist.flReaders fl [] }}

end spec

end Bbolt
end EtcdGrove
end Perennial
