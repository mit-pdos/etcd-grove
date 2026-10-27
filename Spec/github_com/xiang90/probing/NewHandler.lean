/-
`probing.NewHandler()`: the trust boundary (`github.com/xiang90/probing` is names-only; rafthttp
stage 6c, `Transport.Handler`'s prober handler, D39: the prober an axiom). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.net.http.Boundary
public import GeneratedProof.github_com.xiang90.probing

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

/-- **`probing.NewHandler()`**: a handler, for any network `H`, of the requests to `a` routed to
`pat` whose protocol allows any `200` response with no header set (`http.handlerFor`). -/
abbrev probing.NewHandler.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.probing }}
    (App (Val (@! _root_.Perennial.github_com.xiang90.probing.NewHandler)) (Val #()))
  {{ (h : GoInterface), RET #h;
      □ ∀ (H : http.HttpNet GF) (a : GoString) (Rs : IProp GF) (pats : List GoString)
        (pat : GoString),
        (□ ∀ (R : http.HReq) (γk : GName) (w : List w8),
          ⌜R.host = a ∧ http.route pats R.path = some pat⌝ → (H.proto a).resp R γk (W64 200) w) -∗
        ⌜∀ R : http.HReq, http.route pats R.path = some pat → (H.proto a).rhdr R []⌝ -∗
        http.handlerFor H a Rs pats pat h }}

end spec

end EtcdGrove
end Perennial
