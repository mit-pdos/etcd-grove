/-
`s.getCommittedIndex()` (`server.go`): the committed index's atomic, a lower bound of the ghost committed index. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.getCommittedIndex()`, any goroutine: an index the cluster's committed index has reached
(`committedAtLeast`; the committed index's invariant, the request path's unit 4b); for the writer
(`o = some v`, with its half: the ready handler's `updateCommittedIndex`, unit 4c), exactly `v`. -/
abbrev EtcdServer.getCommittedIndex.spec : Prop :=
  ∀ (s : Loc) (γr : ReadNames) (o : Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvCommittedInv s γr ∗ srvCommittedOwnOpt γr o }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"getCommittedIndex")) (Val #()))
  {{ (v : w64), RET #v; committedAtLeast γr v ∗ srvCommittedOwnOpt γr o ∗
      ⌜∀ v₀, o = some v₀ → v = v₀⌝ }}

end spec

end EtcdGrove
end Perennial
