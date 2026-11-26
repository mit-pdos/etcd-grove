/-
**grpc's calls: a stream's ghost names and its dispatched metadata** (`notes/phase7-endstate.md`
§1.2, §1.4). The names of a call (`StreamNames`, moved
here from `InvGrpcStream.lean`, with the dispatch's name `md`, and countable: the call's slot is keyed
by them) and the one fact the client learns of the dispatch: `streamDispIs γ a md`, the stream `γ` was
dispatched to the address `a` with the metadata `md` (persistent, set once; `streamDispIs_agree`).
The call protocol over them (S3.1: `CallParams`, `callInv`, `callDeposit`, `callHeadIs`) is
`InvGrpcCallLib.lean`, which needs the service table and the stream tokens above this module.

**The metadata in ghost state** (a deviation from the plan's text, recorded there in §1.5): a ghost
variable holds a countable value, and `GrpcMd` (a function of the key) is not countable. What is
stored is the address and a finite code of the metadata (`GrpcMdCode`: `none`, or its keys with their
values), and `streamDispIs γ a md` says the stored code denotes `md`. A dispatched metadata is always such a code's:
the server makes it from the finitely many fields of the call's head (`grpcFieldsMd`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcBase
public import Perennial.Ghost.DGhostVar

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- The ghost names of one stream (or unary call): the up queue (the requests the client sent), the
server's received prefix of it, the down queue (the responses the server sent), the up queue's end,
the client's received prefix of the down queue, the down queue's end, (the watch slice's unit W-C)
an auxiliary name the handler sets once (`streamAuxTok`, `streamAuxIs`: the names of the handler's
own per-stream ghost state, allocated after the stream specification is fixed, which the stream
specification can then mention), and (phase 7, SW1) the metadata the call was dispatched with
(`streamDispIs`). -/
structure StreamNames where
  up : GName
  upRcv : GName
  down : GName
  upEnd : GName
  downRcv : GName
  downEnd : GName
  aux : GName
  md : GName

instance StreamNames.countable : Pos.Countable StreamNames :=
  .ofInjective (fun γ => Pos.Countable.encode (γ.up, γ.upRcv, γ.down, γ.upEnd, γ.downRcv,
      γ.downEnd, γ.aux, γ.md))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

/-- **A finite code of a call's metadata** (see the file header): `none`, or the keys with their
values (the first entry of a key is its). -/
abbrev GrpcMdCode : Type := Option (List (GoString × List GoString))

/-- The metadata a code denotes. -/
def GrpcMdCode.md (c : GrpcMdCode) : GrpcMd := c.map fun l k => l.lookup k

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The stream `γ` was dispatched to the address `a` with the metadata `md`** (persistent): set
once, by whoever dispatches it (`ClientConn.NewStream`'s axiom until S3, `call_dispatch` after). Both
are learned by the client with each response (`cliStreamIs`), since a transparent retry before the
stream is committed may recompute the head (its per-RPC credentials called again: R2) and re-pick the
address (`getTransportConn`, the model's `modelChooseAddr`); the two agree (`streamDispIs_agree`).
The server's side gets no interim statement of it (its run is given the metadata through its
context, `grpcStreamSpecAt`); S3's `call_dispatch` gives it. -/
def streamDispIs (γ : StreamNames) (a : GoString) (md : GrpcMd) : IProp GF :=
  iprop(∃ c : GrpcMdCode, ⌜c.md = md⌝ ∗ dghostVar γ.md DFrac.discard (some (a, c)))

instance streamDispIs_persistent (γ : StreamNames) (a : GoString) (md : GrpcMd) :
    Persistent (streamDispIs (GF := GF) γ a md) := by
  unfold streamDispIs; infer_instance

/-- Two dispatches of one stream agree. -/
theorem streamDispIs_agree (γ : StreamNames) (a a' : GoString) (md md' : GrpcMd) :
    streamDispIs (GF := GF) γ a md ∗ streamDispIs γ a' md' ⊢ ⌜a = a' ∧ md = md'⌝ := by
  unfold streamDispIs
  iintro ⟨⟨%c, %hc, H1⟩, ⟨%c', %hc', H2⟩⟩
  ihave %H := dghostVar_agree γ.md (some (a, c)) DFrac.discard (some (a', c')) DFrac.discard $$ H1 H2
  ipureintro
  cases H
  exact ⟨rfl, by rw [← hc, ← hc']⟩

end defs

end EtcdGrove
end Perennial
