/-
**The stream handler's close notifier** (rafthttp stage 5e-2): `closeNotifier`, the closer a
stream connection carries (`outgoingConn.Closer`), whose `Close` hands a resource `P` (the
handler's response writer, `connBack`) to the handler waiting on `closeNotify()`. Lean-first.

`Close` closes the `done` channel, a broadcast channel (Perennial's idiom, whose receivers get a
persistent fact): the fact is an invariant holding `P` or the handler's token (`cnTok`, a ticket);
the handler, the token's only holder, swaps it for `P` (`cn_take`), once.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Writer
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The close notifier's invariants' namespace. -/
def cnN : Namespace := nroot.@"rafthttp_closeNotifier"

/-- **The handler's token** (exclusive): what it swaps for `P`. -/
abbrev cnTok (γ : GName) : IProp GF := http.reqTicket γ

/-- **What a closed notifier's receivers learn** (persistent): `P`, or the token once taken. -/
def cnQ (γ : GName) (P : IProp GF) : IProp GF := iprop(inv cnN iprop(P ∨ cnTok γ))

instance cnQ_persistent (γ : GName) (P : IProp GF) : Persistent (cnQ γ P) := by
  unfold cnQ; infer_instance

/-- **The notifier `n`, to wait on** (persistent): its `done` channel. -/
def cnRecv (n : Loc) (γ : GName) (P : IProp GF) : IProp GF :=
  iprop(∃ (dc : GoChan) (γc : ChanNames), n.[rafthttp.closeNotifier, go!"done"] ↦□ dc ∗
    ownBroadcastChan dc γc (cnQ γ P) .Unknown)

instance cnRecv_persistent (n : Loc) (γ : GName) (P : IProp GF) : Persistent (cnRecv n γ P) := by
  unfold cnRecv; infer_instance

/-- **The right to close the notifier `n`** (exclusive, once). -/
def cnClose (n : Loc) (γ : GName) (P : IProp GF) : IProp GF :=
  iprop(∃ (dc : GoChan) (γc : ChanNames), n.[rafthttp.closeNotifier, go!"done"] ↦□ dc ∗
    ownBroadcastChan dc γc (cnQ γ P) .Pending)

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The handler takes `P`** with its token, from a closed notifier's fact. -/
theorem cn_take (γ : GName) (P : IProp GF) :
    ⊢ cnQ γ P -∗ cnTok γ ={⊤}=∗ ▷ P := by
  iintro #Hq Htok
  unfold cnQ
  iinv Hq with Hi Hclose
  icases Hi with (HP | Htok')
  · imod Hclose $$ [Htok] with -
    · inext; iright; iexact Htok
    imodintro; iexact HP
  · ihave Hf : ▷ (False ∗ False) $$ [Htok Htok']
    · inext
      iexfalso
      iapply http.reqTicket_excl γ $$ [$Htok $Htok']
    icases Hf with ⟨Hf1, Hf2⟩
    imod Hclose $$ [Hf1] with -
    · inext; iexfalso; iexact Hf1
    imodintro; inext; iexfalso; iexact Hf2

end lemmas

end EtcdGrove
end Perennial
