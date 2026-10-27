/-
`path.Base` (`path.go`; rafthttp stage 5d). Lean-first; the model: `Proof/path/Model.lean`.
-/
module

public import Proof.path.Model
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `Base(p)`: the last element of `p` (`path.baseModel`). -/
abbrev path.Base.spec : Prop :=
  ∀ (p : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.path }}
    (App (Val (@! _root_.Perennial.path.Base)) (Val #p))
  {{ (r : GoString), RET #r; ⌜r = path.baseModel p⌝ }}

end spec

end EtcdGrove
end Perennial
