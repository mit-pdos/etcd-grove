/-
**grpc's calls: a stream's ghost names and its dispatched metadata** (phase 7, SW1, 2026-11-24;
`notes/phase7-endstate.md` §1.2, §1.4). The defs module the call protocol (S3.1: `CallParams`,
`callInv`, `callDeposit`, `callHeadIs`) grows in; for now the names of a call (`StreamNames`, moved
here from `InvGrpcStream.lean`, with the dispatched metadata's name `md`, and countable: the call's
slot is keyed by them) and the one fact both ends learn of the dispatch: `streamMdIs γ md`, the
stream `γ` was dispatched with the metadata `md` (persistent, set once; `streamMdIs_agree`).

**The metadata in ghost state** (a deviation from the plan's text, recorded there in §1.5): a ghost
variable holds a countable value, and `GrpcMd` (a function of the key) is not countable. What is
stored is a finite code of the metadata (`GrpcMdCode`: `none`, or its keys with their values), and
`streamMdIs γ md` says the stored code denotes `md`. A dispatched metadata is always such a code's:
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
(`streamMdIs`). -/
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

/-- **The stream `γ` was dispatched with the metadata `md`** (persistent): set once, by whoever
dispatches it (`ClientConn.NewStream`'s axiom until S3, `call_dispatch` after); the client learns it
with the first response (`cliStreamIs`), the server from its run's context. Both agree on it
(`streamMdIs_agree`). -/
def streamMdIs (γ : StreamNames) (md : GrpcMd) : IProp GF :=
  iprop(∃ c : GrpcMdCode, ⌜c.md = md⌝ ∗ dghostVar γ.md DFrac.discard (some c))

instance streamMdIs_persistent (γ : StreamNames) (md : GrpcMd) :
    Persistent (streamMdIs (GF := GF) γ md) := by
  unfold streamMdIs; infer_instance

/-- Two dispatched metadata of one stream agree. -/
theorem streamMdIs_agree (γ : StreamNames) (md md' : GrpcMd) :
    streamMdIs (GF := GF) γ md ∗ streamMdIs γ md' ⊢ ⌜md = md'⌝ := by
  unfold streamMdIs
  iintro ⟨⟨%c, %hc, H1⟩, ⟨%c', %hc', H2⟩⟩
  ihave %H := dghostVar_agree γ.md (some c) DFrac.discard (some c') DFrac.discard $$ H1 H2
  ipureintro
  cases H
  rw [← hc, ← hc']

end defs

end EtcdGrove
end Perennial
