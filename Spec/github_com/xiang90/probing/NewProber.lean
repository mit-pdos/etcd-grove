/-
`probing.NewProber(rt)`: the trust boundary (`github.com/xiang90/probing` is names-only; rafthttp
stage 6c, `Transport.Start`'s probers, D39: the prober an axiom). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import GeneratedProof.github_com.xiang90.probing

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A prober** (`probing.Prober`, an interface): its `RemoveAll()` returns (`Transport.Stop`'s).
`probing.NewProber` returns one. -/
def probing.proberOk (p : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜p = GoInterface.ok ti⌝ ∗
    {{ True }} (App (Val #(methods ti.ty go!"RemoveAll" ti.v)) (Val #())) {{ RET #(); True }})

instance probing.proberOk_persistent (p : GoInterface) : Persistent (probing.proberOk (GF := GF) p) := by
  unfold probing.proberOk; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`probing.NewProber(rt)`**: a prober (`probing.proberOk`). -/
abbrev probing.NewProber.spec : Prop :=
  ∀ (rt : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.probing }}
    (App (Val (@! _root_.Perennial.github_com.xiang90.probing.NewProber)) (Val #rt))
  {{ (p : GoInterface), RET #p; probing.proberOk p }}

end spec

end EtcdGrove
end Perennial
