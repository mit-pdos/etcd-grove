/-
`(*snap.Snapshotter).SaveDBFrom(r, id)` (`server/etcdserver/api/snap/db.go`), as etcd PR #22046
changes it: on success it marks `id` pending apply. Lean-first (no Rocq counterpart); branch
`pr-verify/etcd-22046` only. See `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/snap/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs

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

/-- `s.SaveDBFrom(r, id)`, reading the database from `r` (an `io.Reader` that `io.Copy` may read
to its end, `ioReader r`): logically atomic on the pending set `M`. It returns a nil error
(`ok = true`) only after adding `id` to the set, at its linearization point (`markPendingDB`,
after the file `<id>.snap.db` is in place and its directory synced); otherwise (`ok = false`)
it returns an error and leaves the set as it was. -/
abbrev snap.Snapshotter.SaveDBFrom.spec : Prop :=
  ∀ (s : Loc) (γ : GName) (dir : GoString) (r : GoInterface) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.snap ∗
      isSnapshotter s γ dir ∗ ioReader r }}
  <<{ ∀∀ M, snapPending γ M }>>
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.snap.Snapshotter.ty
      @!! go!"SaveDBFrom")) (Val #r)) (Val #id)) @@ ∅
  <<{ ∃∃ (ok : Bool), snapPending γ (if ok then GMap.insert id () M else M) }>>
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      if ok then ⌜err = interface.nil⌝
      else ∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗ fmt.stringMethodSpec e go!"Error" }}

end spec

end EtcdGrove
end Perennial
