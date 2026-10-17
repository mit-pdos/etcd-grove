/-
`errors.As(err, target)` with `err` of exactly the target's element type: the trust boundary
(PR etcd#22243, the peer hashKV handler's `MaxBytesError` check). Perennial's `errors.As.spec`
says only that `As` returns some boolean (it does not model the assignability check, which is by
reflection); Go's `As` (`errors/wrap.go`) first checks `reflectlite.TypeOf(err).AssignableTo(targetType)`,
which holds when the types are identical, and then stores `err` into `*target` and returns
`true`. `AsTarget T` excludes its panic. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvHashKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3
  go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `errors.As(err, target)`, `err` an error of dynamic type `*T` (value `m`) and `target` a
`**T` (`l`), stores `m` in `*l` and returns `true`. -/
abbrev errors.AsExact.spec : Prop :=
  ∀ (T : go.GoType) (m l v : Loc),
  _root_.Perennial.errors.AsTarget (go.GoType.PointerType T) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ l ↦ v }}
    (App (App (Val (@! _root_.Perennial.errors.As))
        (Val #(interface.mkOk (go.GoType.PointerType T) #m)))
      (Val #(interface.mkOk (go.GoType.PointerType (go.GoType.PointerType T)) #l)))
  {{ RET #true; l ↦ m }}

end spec

end EtcdGrove
end Perennial
