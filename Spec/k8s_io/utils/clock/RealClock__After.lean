/-
`clock.RealClock.After(d)` (`k8s.io/utils/clock`, names-only: it is `time.After(d)`). **A named
hypothesis** (outside client-go, no axiom this round; the reflector's `watch` waits on it to back
off; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round): `?` in
`etc/link-lean-first-k8scache.txt`. Stated as Perennial's proof of `time.After` gives: a channel
some goroutine sends a time on (a `isChanBag` with no resource).
-/
module

public import Proof.k8s_io.utils.clock.Init
public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `RealClock{}.After(d)`: a channel some time is sent on. -/
abbrev clock.RealClock.After.spec : Prop :=
  ∀ (c : k8s_io.utils.clock.RealClock) (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock }}
    (App (Val (c @!! k8s_io.utils.clock.RealClock.ty @!! go!"After")) (Val #d))
  {{ (ch : Loc) (γ : ChanNames), RET #ch; isChanBag (V := time.Time) γ ch (fun _ => iprop(True)) }}

end spec

end EtcdGrove
end Perennial
