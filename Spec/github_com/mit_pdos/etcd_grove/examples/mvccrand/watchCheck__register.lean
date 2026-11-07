/- Lean-first (no Rocq counterpart).

`c.register(ws, r, ticks)` (`examples/mvccrand/mvccrand.go`): for each tick (the ticks channel's
consumer, `isTicks`, `WriterRun.lean`: each value a published revision), a watcher of a random key
and end from a start revision in `[1, pub + 1]`, registered on the stream `ws` under `c.mu`; an
empty range fails with `ErrEmptyWatcherRange` and id `-1`, any other is registered without error
(the stream open: the registrar's half of `γ.cl` at `false`, `World.lean`), its watcher added to
the lock's map and registry (`WatchLock.lean`); now and then a progress request. Every check
passes; at the channel's close, the store's reader token and the registrar's half of `γ.cl` back.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WatchLock
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WriterRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev watchCheck.register.spec : Prop :=
  ∀ (c : Loc) (γ : RandNames) (h : Loc) (wm : GoMap) (ws : GoInterface) (r : Loc) (g : rng)
    (γt : SpscNames) (ch : GoChan) (rcvd : List w64),
  {{ wcCtx c γ h wm ∗ isMvccWatchStream ws γ.kv γ.ws ∗ mvccReaders γ.kv 1 ∗ r ↦ g ∗
      isTicks γt ch γ ∗ spscConsumer (V := w64) γt rcvd ∗ ghostVar γ.cl (1 : Qp).half false }}
    (App (App (App (Val (c @!! go.GoType.PointerType watchCheck.ty @!! go!"register")) (Val #ws))
      (Val #r)) (Val #ch))
  {{ RET #(); mvccReaders γ.kv 1 ∗ ghostVar γ.cl (1 : Qp).half false ∗ ∃ g' : rng, r ↦ g' }}

end spec

end mvccrand
end EtcdGrove
end Perennial
