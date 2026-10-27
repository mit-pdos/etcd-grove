/-
`rate.Every(d)`: the trust boundary (`golang.org/x/time/rate` is names-only; rafthttp stage 6c,
`Transport.Start`'s default dial-retry rate). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import GeneratedProof.golang_org.x.time.rate

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

/-- **`rate.Every(d)`**: some limit (a `float64`'s bits). -/
abbrev rate.Every.spec : Prop :=
  ∀ (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate }}
    (App (Val (@! _root_.Perennial.golang_org.x.time.rate.Every)) (Val #d))
  {{ (l : w64), RET #l; True }}

end spec

end EtcdGrove
end Perennial
