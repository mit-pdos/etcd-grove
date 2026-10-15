/-
`pkg/wait` (the wait registry): the contract its `New` establishes (`isWait`), used by the
server's request path (the proposer's `Register`/`Trigger(id, nil)`, `etcdserver/InvRequest.lean`)
and the apply thread (`Trigger(id, result)`, `IsRegistered`). Lean-first (no Rocq counterpart);
moved here from the server's `InvRequest.lean` (unit 0 of the request path) and made the specs of
`wait.New` in unit 2 (2026-10-12). The list's own invariant (the shards' locks and maps) is
`wait/List.lean`, its proofs' alone.

**The contract** (`isWait w γi γw R RD`), generic in the registration condition `R : id →
expectation → IProp` (persistent):
* `Register(id)`, with the id's slot (`idSlot γi id`, from the generator: so the code's
  `log.Panicf("dup id")` never runs) and an expectation `Ψ` with `□ R id Ψ`, returns a channel
  the caller receives `Ψ`'s value from (`waitRecv`: a handoff channel, buffer 1, sent once then
  closed, `cache/v3/Handoff.lean`), and the persistent record that `id` was registered with that
  channel's consumer token (`waitRegd γw id γh.takenName`, a ghost map of every id ever
  registered);
* `Trigger(id, x)` takes, from anyone, `Ψ x` for every `Ψ` `R` allows under `id` (`waitTrig`), or,
  from the registering proposer giving up (`x = nil`), its consumer token with the record (which
  identifies the channel `id` is registered with, if it still is: the token goes into the channel
  with the `nil`, so the proposer, having given it up, can never receive);
* `IsRegistered(id)` returns a boolean, with the reader's resource `RD` (the shards' reader
  slots of their `RWMutex`es: Perennial's `RWMutex` admits a bounded number of readers, so a
  reader holds a token; `New` returns `RD` once, to the apply thread, the only reader); to a
  caller that knows `id` was registered (`waitRegd γw id t`), `false` means the registration is
  gone (`waitGone γw id t`: a `Trigger` took it out, its channel has its value or is getting it;
  the request path's unit 4d, 2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.go_etcd_io.etcd.cache.v3.Handoff
public import Perennial.Ghost.DGhostVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section wait
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What the registered channel carries: the expectation's value, or `nil` from the proposer
giving up (`Trigger(id, nil)`, with its consumer token, which it then no longer has). -/
def waitVal (γh : HandoffNames) (Ψ : GoInterface → IProp GF) (x : GoInterface) : IProp GF :=
  iprop(Ψ x ∨ (⌜x = GoInterface.nil⌝ ∗ handoffConsumer γh false))

/-- **The proposer's receive right** on the channel `ch` `Register(id)` returned, for `Ψ`: a
handoff channel of `waitVal`, never closed without a send (`Trigger` sends, then closes: the
close's resource `False`, so the proposer's receive gets a value), and its consumer token
(nothing taken yet). -/
def waitRecv (γh : HandoffNames) (ch : Loc) (Ψ : GoInterface → IProp GF) : IProp GF :=
  iprop(isHandoff (V := GoInterface) γh ch (waitVal γh Ψ) iprop(True) iprop(False) ∗
    handoffConsumer γh false)

/-- **`id` was registered** (persistent) with a channel whose consumer token is named `t`: the
names of `id`'s shard (`id % 64`) in the wait's ghost map `γw` (the shard's live map `γs`, its
record `γr` of every id ever registered there; `wait/List.lean`), and `id`'s element of `γr`: `t`
and the name `g` of the registration's flag, exclusive while the registration is live, discarded
(`waitGone`) once a `Trigger` took it out. (An id is registered at most once: `Register` takes the
id's slot.) -/
def waitRegd (γw : GName) (id : w64) (t : GName) : IProp GF :=
  iprop(∃ (γs γr g : GName), (id % W64 64) ↪[γw]□ (γs, γr) ∗ id ↪[γr]□ (t, g))

instance waitRegd_persistent (γw : GName) (id : w64) (t : GName) :
    Persistent (waitRegd (GF := GF) γw id t) := by
  unfold waitRegd; infer_instance

/-- **`id`'s registration is gone** (persistent): it was registered (with the consumer token
named `t`) and a `Trigger(id, _)` took it out of the registry since, so its channel has been or
is being sent its one value (the expectation's, or the proposer's `nil` with its consumer token):
`IsRegistered(id)` returning `false` to a caller that knew of the registration says this. -/
def waitGone (γw : GName) (id : w64) (t : GName) : IProp GF :=
  iprop(∃ (γs γr g : GName), (id % W64 64) ↪[γw]□ (γs, γr) ∗ id ↪[γr]□ (t, g) ∗
    dghostVar g DFrac.discard ())

instance waitGone_persistent (γw : GName) (id : w64) (t : GName) :
    Persistent (waitGone (GF := GF) γw id t) := by
  unfold waitGone; infer_instance

/-- A gone registration was a registration. -/
theorem waitGone_regd (γw : GName) (id : w64) (t : GName) :
    waitGone (GF := GF) γw id t ⊢ waitRegd γw id t := by
  unfold waitGone waitRegd
  iintro ⟨%γs, %γr, %g, #H1, #H2, -⟩
  iexists γs, γr, g
  iframe #

/-- What the caller of `IsRegistered(id)` knows of `id`'s registration: nothing (`none`), or that
it was registered with the consumer token named `t` (`some t`). -/
def waitRegdOpt (γw : GName) (id : w64) : Option GName → IProp GF
  | none => iprop(True)
  | some t => waitRegd γw id t

instance waitRegdOpt_persistent (γw : GName) (id : w64) (ot : Option GName) :
    Persistent (waitRegdOpt (GF := GF) γw id ot) := by
  cases ot <;> unfold waitRegdOpt <;> infer_instance

/-- What `IsRegistered(id)` returning `false` tells that caller: nothing, or that the
registration it knew of is gone. -/
def waitGoneOpt (γw : GName) (id : w64) : Option GName → IProp GF
  | none => iprop(True)
  | some t => waitGone γw id t

instance waitGoneOpt_persistent (γw : GName) (id : w64) (ot : Option GName) :
    Persistent (waitGoneOpt (GF := GF) γw id ot) := by
  cases ot <;> unfold waitGoneOpt <;> infer_instance

/-- **What `Trigger(id, x)` takes from anyone but the proposer**: `Ψ x` for every expectation
registered under `id` (by the registration condition `R`). Trivial if nothing is registered
(another member's request, or a registration already triggered: then nothing is sent). -/
def waitTrig (R : w64 → (GoInterface → IProp GF) → IProp GF) (id : w64) (x : GoInterface) :
    IProp GF :=
  iprop(∀ Ψ, R id Ψ -∗ Ψ x)

/-- **The `wait.Wait` `w`** (persistent: the contract `New` establishes; see the file header),
with the ids' names `γi` (their wait slots), the registered ids' ghost map `γw`, the
registration condition `R` (persistent) and the reader's resource `RD`. -/
def isWait (w : GoInterface) (γi : IdNames) (γw : GName)
    (R : w64 → (GoInterface → IProp GF) → IProp GF) (RD : IProp GF) : IProp GF :=
  iprop(∃ wi : GoInterfaceOk, ⌜w = GoInterface.ok wi⌝ ∗
    □ (∀ (id : w64) (Ψ : GoInterface → IProp GF),
      {{ idSlot γi id ∗ □ R id Ψ }}
        (App (Val #(methods wi.ty go!"Register" wi.v)) (Val #id))
      {{ (ch : Loc), RET #ch; ∃ γh, waitRecv γh ch Ψ ∗ waitRegd γw id γh.takenName }}) ∗
    □ (∀ (id : w64) (x : GoInterface),
      {{ (∃ γh : HandoffNames, ⌜x = GoInterface.nil⌝ ∗ handoffConsumer γh false ∗
            waitRegd γw id γh.takenName) ∨ waitTrig R id x }}
        (App (App (Val #(methods wi.ty go!"Trigger" wi.v)) (Val #id)) (Val #x))
      {{ RET #(); True }}) ∗
    □ (∀ (id : w64) (ot : Option GName),
      {{ RD ∗ waitRegdOpt γw id ot }}
        (App (Val #(methods wi.ty go!"IsRegistered" wi.v)) (Val #id))
      {{ (b : Bool), RET #b; RD ∗ (⌜b = true⌝ ∨ waitGoneOpt γw id ot) }}))

instance isWait_persistent (w : GoInterface) (γi : IdNames) (γw : GName)
    (R : w64 → (GoInterface → IProp GF) → IProp GF) (RD : IProp GF) :
    Persistent (isWait (GF := GF) w γi γw R RD) := by
  unfold isWait; infer_instance

end wait

end EtcdGrove
end Perennial
