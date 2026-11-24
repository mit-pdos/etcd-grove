/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: one call of `Svc.Echo`, as net/rpc's client specs take it

The instance of `Client.Call.spec` (and of the `Go` path's `callPost`) for the driver's request
`pa` (`Args{id, data, fail}`, its payload `dsl`) and reply `pr` (`&Reply{}`): the continuation
`echoPhi` (pure: `answerOk`), the decoding outcome `echoTheta`, the argument resources `echoRargs`
and the reply's `echoD`; the deposit (`echo_enc`: the codec's encoding of the request with
`echoSpec`'s deposit, the id's token), the reply's decoding (`echo_dec`), and the outcome as `check`
takes it (`echo_outcome_*`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.CodecProof
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.check

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.wire

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The call's continuation: what the client may read back (`answerOk`). -/
def echoPhi (id : w64) (data : List w8) (fail : GoString) (rep : List w8) (msg : GoString) :
    IProp GF :=
  iprop(⌜answerOk id data fail rep msg⌝)

/-- The request's resources, given back after its encoding. -/
def echoRargs (pa : Loc) (id : w64) (dsl : GoSlice) (data : List w8) (fail : GoString) :
    IProp GF :=
  iprop(pa ↦ service.Args.mk id dsl fail ∗ dsl ↦* data)

/-- The reply's resource: `&Reply{}`. -/
def echoD (pr : Loc) : IProp GF := iprop(pr ↦ service.Reply.mk (W64 0) slice.nil (W64 0))

/-- The reply's decoding outcome: on success, the method's reply to this request. -/
def echoTheta (pr : Loc) (id : w64) (data : List w8) (fail : GoString) (rep : List w8)
    (ok : Bool) : IProp GF :=
  if ok then iprop(⌜fail = []⌝ ∗ ∃ dsl' : GoSlice, pr ↦ service.Reply.mk id dsl' (W64 1) ∗
    dsl' ↦* data) else iprop(True)

/-- The request's encoding carries `echoSpec`'s deposit (the id's token). -/
theorem echo_enc (L : CodecLaws (GF := GF)) (γid : GName) (pa : Loc) (id : w64) (dsl : GoSlice)
    (data : List w8) (fail : GoString) (hlen : data.length ≤ 64) (hfail : fail = [] ∨ fail ∈ failList) :
    (pa ↦ service.Args.mk id dsl fail ∗ dsl ↦* data ∗ idTok γid id : IProp GF) ⊢
      drvCodec.enc (ptrIface service.Args.ty pa) (fun bs => iprop(⌜bs.length ≤ net.rpc.maxFrameN⌝ ∗
        echoSvc γid go!"Echo" bs (echoPhi id data fail) ∗ echoRargs pa id dsl data fail)) := by
  iintro ⟨Ha, Hd, Htok⟩
  iapply L.enc_Args pa (DFrac.own 1) id dsl fail (DFrac.own 1) data
  iframe Ha Hd
  iintro Ha Hd
  isplitr
  · ipureintro
    have hf : fail.length ≤ 19 := by
      rcases hfail with rfl | h
      · simp
      · simp only [failList, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl <;> decide
    have hm := len_flatten_encU8 data
    have hfs : (fStr fail).length ≤ 1 + (8 + fail.length) := by
      unfold fStr fld encStr; split <;> simp [u64Le_length] <;> omega
    have hfb : (fBytes data).length ≤ 1 + (8 + 8 * data.length) := by
      unfold fBytes fld; rw [encBytes_eq]; split <;> simp [u64Le_length, hm] <;> omega
    have hfi : (fU64 id).length ≤ 9 := by
      unfold fU64 fld; split <;> simp [u64Le_length] <;> omega
    simp only [encArgs, tagged, strct, encStr, List.flatten_cons, List.flatten_nil,
      List.length_append, List.length_cons, List.append_nil, u64Le_length, net.rpc.maxFrameN, tArgs,
      List.length_nil]
    have : (go!"github.com/mit-pdos/etcd-grove/examples/net/rpcdriver/service.Args").length ≤ 100 := by
      decide
    omega
  isplitr [Ha Hd]
  · unfold echoSvc
    simp only [↓reduceIte]
    unfold echoSpec
    iexists id, data, fail
    iframe Htok
    isplitr
    · ipureintro; rfl
    isplit
    · iintro %hf; unfold echoPhi; ipureintro; exact .inl ⟨hf, rfl, rfl⟩
    isplit
    · iintro %hf; unfold echoPhi; ipureintro; exact .inr (.inl ⟨hf, rfl, rfl⟩)
    · iintro %msg %hm; unfold echoPhi; ipureintro; exact .inr (.inr ⟨hm, rfl⟩)
  · unfold echoRargs; iframe Ha Hd

/-- The reply's decoding, of the replies the method's answers deliver. -/
theorem echo_dec (L : CodecLaws (GF := GF)) (pr : Loc) (id : w64) (data : List w8)
    (fail : GoString) :
    ⊢ □ (echoD pr -∗ ∀ rep, echoPhi (GF := GF) id data fail rep [] -∗
      drvCodec.dec rep (ptrIface service.Reply.ty pr) (echoTheta pr id data fail rep)) := by
  imodintro
  iintro HD %rep Hrep
  iunfold echoPhi at Hrep
  icases Hrep with %Hrep
  unfold answerOk at Hrep
  rcases Hrep with ⟨hf, -, rfl⟩ | ⟨hf, hm, -⟩ | ⟨hm, -⟩
  · iapply L.dec_Reply pr id data (W64 1)
    unfold echoD
    iframe HD
    iintro %dsl' Hr Hd'
    unfold echoTheta
    simp only [↓reduceIte]
    iframe Hr Hd'
    ipureintro; exact hf
  · exact absurd hm.symm hf
  · exact absurd rfl (net.rpc.srvErrMsg_ne _ hm)

end defs

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

end Perennial
