/-
`(*rate.Limiter).Wait` (rafthttp stage 5c, the stream reader's dial retries; rate-wait, 2026-11-23:
proved over the real code, until then the trust boundary). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.context
public import Perennial.Proof.sync.Base
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
variable [sem : go.Semantics]
variable [package_sem : golang_org.x.time.rate.Assumptions]

/-- The fields of the limiter `rl` its mutex guards: all but `mu` (x/time/rate v0.16.0, `rate.go`:
every method reads and writes `limit`, `burst`, `tokens`, `last` and `lastEvent` only with `lim.mu`
held; `NewLimiter` initializes them before the limiter is shared). -/
def rate.limiterFields (rl : Loc) : IProp GF :=
  iprop(∃ (l : golang_org.x.time.rate.Limit) (b tk : w64) (la le : _root_.Perennial.time.Time),
    rl.[golang_org.x.time.rate.Limiter, go!"limit"] ↦ l ∗
    rl.[golang_org.x.time.rate.Limiter, go!"burst"] ↦ b ∗
    rl.[golang_org.x.time.rate.Limiter, go!"tokens"] ↦ tk ∗
    rl.[golang_org.x.time.rate.Limiter, go!"last"] ↦ la ∗
    rl.[golang_org.x.time.rate.Limiter, go!"lastEvent"] ↦ le)

/-- `rate.limiterOk`'s fact, raw: `rl`'s mutex guards its fields (prove-smalllibs, 2026-11-20:
until then opaque; `NewLimiter` is proved over the real code). -/
def rate.limiterRaw (rl : Loc) : IProp GF :=
  _root_.Perennial.sync.isMutex (rl.[golang_org.x.time.rate.Limiter, go!"mu"]) (rate.limiterFields rl)

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
variable [package_sem : golang_org.x.time.rate.Assumptions]

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
