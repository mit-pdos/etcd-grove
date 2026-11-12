/-
`shouldStream(opts)` (`k8s.io/apiserver/pkg/storage/etcd3/store.go:748-760`) returns `false`: not
recursive, or a limit with a non-empty predicate, or else `EtcdRangeStream` is off
(`rangeStreamOff`, B5's `Enabled` triple) and `&&` does not call `Supports`. Proved (stage 7e-2,
`notes/k8s-7e-2-draft.md` §3.1). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs
public import Proof.k8s_io.apiserver.pkg.storage.SelDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev shouldStream.spec : Prop :=
  ∀ (opts : k8s_io.apiserver.pkg.storage.ListOptions) (Obj : Type) (S : ObjSpec GF Obj)
    (sel : Obj → Bool) (emp : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗
      selPredOk S opts.Predicate' sel emp ∗ rangeStreamOff }}
    (App (Val (@! k8s_io.apiserver.pkg.storage.etcd3.shouldStream)) (Val #opts))
  {{ RET #false; True }}

end spec

end k8s
end EtcdGrove
end Perennial
