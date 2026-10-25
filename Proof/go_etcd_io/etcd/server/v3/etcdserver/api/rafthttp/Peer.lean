/-
**A peer's stream writers** (rafthttp stage 5e-2): what the stream handler needs of the peer it
attaches a connection to. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Writer

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

/-- **The peer `p` of `pid` at the member `lid`, its stream writers** (persistent): its logger (not
`nil`), and its two stream writers, of `lid` to `pid` (`swFixed`). -/
def peerStreams (Rh : RaftHttp GF) (lid pid : w64) (p : Loc) : IProp GF :=
  iprop(∃ (lg cw2 cw1 : Loc) (Rr2 Rr1 : IProp GF),
    p.[rafthttp.peer, go!"lg"] ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    p.[rafthttp.peer, go!"msgAppV2Writer"] ↦□ cw2 ∗ swFixed Rh .msgAppV2 lid pid Rr2 cw2 ∗
    p.[rafthttp.peer, go!"writer"] ↦□ cw1 ∗ swFixed Rh .message lid pid Rr1 cw1)

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 16384 in
instance peerStreams_persistent (Rh : RaftHttp GF) (lid pid : w64) (p : Loc) :
    Persistent (peerStreams Rh lid pid p) := by
  unfold peerStreams; infer_instance

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An attached connection's type and closer (read-only). -/
theorem outConnOk_fields (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (conn : Loc) :
    outConnOk Rh ty lid pid conn ⊢ outConnOk Rh ty lid pid conn ∗
      conn.[rafthttp.outgoingConn, go!"t"] ↦□ ty.str := by
  iintro Hc
  iunfold outConnOk at Hc
  icases Hc with ⟨%wi, %cl, %a, %R, %γk, %γw, #Ht, #Hw, #Hf, #Hcl, #Hl, #Hp, Hrw, #Hreg, %HR, Hclr⟩
  iframe #
  iunfold outConnOk
  iexists wi, cl, a, R, γk, γw
  iframe; iframe #
  ipureintro; exact HR

/-- **Closing an attached connection that was not taken**: the closer gets its writer back. -/
theorem outConnOk_close (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (conn : Loc) :
    outConnOk Rh ty lid pid conn ⊢ ∃ cl : GoInterface,
      conn.[rafthttp.outgoingConn, go!"Closer"] ↦□ cl ∗ ∃ Q : IProp GF, closeRight cl Q ∗ Q := by
  iintro Hc
  iunfold outConnOk at Hc
  icases Hc with ⟨%wi, %cl, %a, %R, %γk, %γw, -, -, -, #Hcl, -, -, Hrw, -, -, Hclr⟩
  iexists cl
  isplitr
  · iexact Hcl
  iexists (connBack Rh wi a R γk)
  isplitl [Hclr]
  · iexact Hclr
  iunfold connBack
  iexists _, _
  iexact Hrw

end lemmas

end EtcdGrove
end Perennial
