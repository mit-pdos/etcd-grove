/- Lean-first (no Rocq counterpart).

`c.complete(upto)` (`examples/mvccrand/mvccrand.go`): whether every watcher has received every
change up to revision `upto`, read under `c.mu` (`cmuInv`, `WatchLock.lean`) through `expect`, for a
lower bound `Hlb` of the history that has `upto` (so `expect`'s `changesAt` checks hold). It makes
no check: the answer is only reported (`Report.WatchersComplete`), so the spec states none of it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WatchLock

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
abbrev watchCheck.complete.spec : Prop :=
  ∀ (c : Loc) (γ : RandNames) (h : Loc) (wm : GoMap) (Hlb : List HRev) (upto : w64),
  sint.Z upto < Hlb.length → sint.Z upto < 2 ^ 63 - 1 →
  {{ wcCtx c γ h wm ∗ histRd h γ.h ∗ monoListLbOwn γ.h.l Hlb }}
    (App (Val (c @!! go.GoType.PointerType watchCheck.ty @!! go!"complete")) (Val #upto))
  {{ (b : Bool), RET #b; histRd h γ.h }}

end spec

end mvccrand
end EtcdGrove
end Perennial
