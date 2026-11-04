/-
`channelContext.Err()` (`k8s.io/apimachinery/pkg/util/wait`, `wait.go:133`; translated,
2026-11-04): `select { case <-c.stopCh: return context.Canceled; default: return nil }`. Lean-first.

The channel is a broadcast channel (only closed, `Perennial/Golang/Theory/Chan/Idioms/Broadcast.lean`)
seen through its internal names `γi` (`isBroadcastChanInternal`), whose done flag
(`dghostVar γi.doneGn .discard true`) holds exactly when it is closed. `Err()` returns `nil` while
the channel is open (so not after the flag was seen: `cl = .Done`), and `Canceled`'s value once it is
closed, the flag then known. A caller that makes the flag a context's closed flag
(`ContextClosed ⟨γi.doneGn, γi.doneGn⟩`) gets Go's `Err` contract (grpc's `ctxErrs`).
-/
module

public import Proof.k8s_io.apimachinery.pkg.util.wait.Init
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

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

/-- `channelContext{stopCh: sc}.Err()`: `nil` while `sc` is open, `Canceled`'s value once it is
closed (see the file header). -/
abbrev wait.channelContext.Err.spec : Prop :=
  ∀ (sc : GoChan) (γs : ChanNames) (γi : BroadcastInternalNames) (Q : IProp GF) (cl : Broadcast),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait ∗
      isBroadcastChanInternal sc γs γi Q ∗
      (match cl with
       | .Done => dghostVar γi.doneGn .discard true
       | _ => iprop(True)) }}
    (App (Val (k8s_io.apimachinery.pkg.util.wait.channelContext.mk sc @!!
      k8s_io.apimachinery.pkg.util.wait.channelContext.ty @!! go!"Err")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil ∧ cl ≠ .Done⌝) ∨
      (globalAddr context.Canceled ↦□ err ∗ dghostVar γi.doneGn .discard true) }}

end spec

end EtcdGrove
end Perennial
