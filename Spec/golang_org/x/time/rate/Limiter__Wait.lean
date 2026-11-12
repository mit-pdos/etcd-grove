/-
`(*rate.Limiter).Wait`: the trust boundary (`golang.org/x/time/rate` is names-only; rafthttp
stage 5c, the stream reader's dial retries). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.context
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import GeneratedProof.golang_org.x.time.rate

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI golang_org.x.time

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- `rate.limiterOk`'s fact, raw (opaque). -/
opaque rate.limiterRaw (rl : Loc) : IProp GF

/-- **`rl` is a rate limiter** (persistent): what `rate.NewLimiter` returns. A `Limiter` is safe
for concurrent use (its methods take its own mutex). -/
def rate.limiterOk (rl : Loc) : IProp GF := iprop(□ rate.limiterRaw rl)

instance rate.limiterOk_persistent (rl : Loc) : Persistent (rate.limiterOk (GF := GF) rl) := by
  unfold rate.limiterOk; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- `rl.Wait(ctx)` of a rate limiter and a context: waits (or not) and returns some error (`nil`
once a token is had; an error if the context is done first, or if the wait would outlast its
deadline). -/
abbrev rate.Limiter.Wait.spec : Prop :=
  ∀ (rl : Loc) (c : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.golang_org.x.time.rate ∗ rate.limiterOk rl ∗
      _root_.Perennial.context.isContext c cd }}
    (App (Val (rl @!! go.GoType.PointerType rate.Limiter.ty @!! go!"Wait"))
      (Val #(GoInterface.ok c)))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
