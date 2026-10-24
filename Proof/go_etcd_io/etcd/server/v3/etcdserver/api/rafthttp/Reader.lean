/-
**The stream reader** (rafthttp stage 5c; `notes/rafthttp-plan.md`, D33d). Lean-first.

A `streamReader` of type `ty` of the local member `lid` pulls the stream the peer `pid` writes for it:
it dials (`GET` the stream's path, with a ticket registered as `(γw, ty, lid)`, `stream_ticket_alloc`),
then decodes the response body's frames (`decodeLoop`) and hands each message to the peer's receive
goroutines (`recvc`, `propc`: bags of `netRecv`, what `Process` takes). What it reads is a prefix of
the stream's bytes (`streamSent`, from the response's protocol, `stream_known`), so each decoded
frame is the writer's frame of that index (`streamSent_frame`): a link heartbeat (dropped) or a
message whose one-shot part it withdraws with its token for that index (`stream_withdraw`).

`paused` and `closer` are guarded by `mu` (`srLockInv`); `stop` closes the body from another
goroutine while `decodeLoop` reads it (`http.respCloser`, a persistent right to close a response's
body: Go's body supports a `Close` concurrent with a `Read`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Writer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.messageDecoder__decode
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.msgAppV2Decoder__decode

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The decoder `dec` of a stream of type `ty`** from `pid` to `lid`, reading `r`, at the codec's
state `s` (exclusive): a `*msgAppV2Decoder` (`v2DecOwn`) or a `*messageDecoder` (its reader,
read-only). -/
def decOwn (lid pid : w64) :
    (ty : StreamTy) → GoInterface → GoInterface → (ty.codec pid lid).S → IProp GF
  | .msgAppV2, dec, r, s => iprop(∃ d : Loc,
      ⌜dec = interface.mkOk (go.GoType.PointerType rafthttp.msgAppV2Decoder.ty) #d⌝ ∗
      v2DecOwn d r pid lid s)
  | .message, dec, r, _ => iprop(∃ d : Loc,
      ⌜dec = interface.mkOk (go.GoType.PointerType rafthttp.messageDecoder.ty) #d⌝ ∗
      d.[rafthttp.messageDecoder, go!"r"] ↦□ r)

/-- **What `mu` guards** of the reader `cr`: `paused`, and `closer`, `nil` or a response body it may
close (`http.respCloser`). -/
def srLockInv (cr : Loc) : IProp GF :=
  iprop(∃ (p : Bool) (c : GoInterface), cr.[rafthttp.streamReader, go!"paused"] ↦ p ∗
    cr.[rafthttp.streamReader, go!"closer"] ↦ c ∗ (⌜c = GoInterface.nil⌝ ∨ http.respCloser c))

/-- **A stream reader's fixed fields** (persistent) of the local member `lid`, reading from `pid`:
its logger (not `nil`), peer id, transport (with `lid`), peer status, mutex, context, and the peer's
receive channels (bags of received messages, `netRecv`: what `Process` takes, `γd` the local
snapshot directory). -/
def srFixed (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (cr : Loc) : IProp GF :=
  iprop(∃ (lg tr ps : Loc) (rc pc : GoChan) (γr γp : ChanNames) (ctx : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)),
    cr.[rafthttp.streamReader, go!"lg"] ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    cr.[rafthttp.streamReader, go!"peerID"] ↦□ pid ∗
    cr.[rafthttp.streamReader, go!"tr"] ↦□ tr ∗ tr.[rafthttp.Transport, go!"ID"] ↦□ lid ∗
    cr.[rafthttp.streamReader, go!"status"] ↦□ ps ∗ peerStatusOk ps ∗
    cr.[rafthttp.streamReader, go!"recvc"] ↦□ rc ∗ isChanBag γr rc (netRecv Rh.γn lid γd) ∗
    cr.[rafthttp.streamReader, go!"propc"] ↦□ pc ∗ isChanBag γp pc (netRecv Rh.γn lid γd) ∗
    sync.isMutex (cr.[rafthttp.streamReader, go!"mu"]) (srLockInv cr) ∗
    cr.[rafthttp.streamReader, go!"ctx"] ↦□ GoInterface.ok ctx ∗ context.isContext ctx cd)

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 16384 in
instance srFixed_persistent (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (cr : Loc) :
    Persistent (srFixed Rh lid pid γd cr) := by
  unfold srFixed; infer_instance

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A prefix of a stream's bytes is a stream's bytes. -/
theorem streamSent_prefix (C : StreamCodec) (N : NetPayload GF) (γw : GName) (rid : w64)
    (w w' : List w8) (h : w' <+: w) :
    ⊢ streamSent C N γw rid w -∗ streamSent C N γw rid w' := by
  unfold streamSent
  iintro ⟨%fr, %s, %Hc, #Hfs⟩
  iexists fr, s
  iframe #
  ipureintro
  exact ⟨Hc.1, h.trans Hc.2⟩

/-- **What the reader knows of the bytes it read**: a prefix of a `200` response's bytes, of the
stream request registered as `(γw, ty, lid)` to the address of `pid`, is a stream's bytes. -/
theorem stream_known (Rh : RaftHttp GF) (R : http.HReq) (γk γw : GName) (ty : StreamTy)
    (lid pid : w64) (bs : List w8) (Hown : Rh.owner R.host = pid) (Hpath : R.path ≠ probingPath) :
    ⊢ streamReg Rh γk (γw, ty, lid) -∗
      (□ ∃ w, ⌜bs <+: w⌝ ∗ ((raftHttpNet Rh).proto R.host).resp R γk (W64 200) w) -∗
      streamSent (ty.codec pid lid) Rh.γn.N γw lid bs := by
  iintro #Hreg #Hw
  icases Hw with ⟨%w, %Hp, Hr⟩
  simp only [raftHttpNet, raftProto]
  icases Hr with ⟨-, Hs⟩
  ihave Hs := Hs $$ %Hpath
  unfold streamResp
  ihave ⟨%c, #Hreg', Hs⟩ := Hs $$ %rfl
  ihave %Hc := streamReg_agree Rh γk _ _ $$ Hreg Hreg'
  subst Hc
  simp only [Hown]
  iapply streamSent_prefix _ _ _ _ w bs Hp $$ Hs

/-- **A response body is a reader** (`readFullAt`) of what the response's protocol allows. -/
theorem respReader_readFullAt (H : http.HttpNet GF) (hRF : http.ReadFull_resp_spec H)
    (rd : GoInterface) (R : http.HReq) (γk : GName) (st : w64) :
    ⊢ readFullAt rd (fun rs => http.respReader H rd R γk st rs)
      (fun bs => iprop(□ ∃ w, ⌜bs <+: w⌝ ∗ (H.proto R.host).resp R γk st w)) := by
  unfold readFullAt
  iintro !> %p %xs %rs %Φ !> ⟨Hp, Hr⟩ HΦ
  wp_apply hRF rd R γk st rs p xs $$ [$Hr $Hp] as %n %err ⟨%ys, %Hys, #HB, Hp, Hr, #Herr⟩
  iapply HΦ
  iexists ys
  iframe; iframe #
  ipureintro
  exact Hys

/-- The message codec's next frame, known to be a stream's bytes, is of an encoding. -/
theorem streamSent_msgFrame (N : NetPayload GF) (γw : GName) (rid : w64)
    (fr : List (MsgWire × List w8)) (s : msgCodec.S) (bs : List w8)
    (Hfr : Chain msgCodec msgCodec.init fr s) :
    ⊢ streamSent msgCodec N γw rid (chainBytes fr ++ msgFrame bs) -∗
      ⌜bs.length < 2 ^ 63 → ∃ st, MsgWireOk st bs⌝ := by
  iintro Hs
  ihave %H := streamSent_compat _ N γw rid fr s (msgFrame bs) Hfr $$ Hs
  ipureintro
  intro hl
  rcases H with h | ⟨w, bs', s1, z1, z2, hf, he⟩
  · have := congrArg List.length h
    simp [msgFrame, u64Be_length] at this
  obtain ⟨st, mbs, -, hw, hml, rfl⟩ := hf
  obtain ⟨rfl, -⟩ := chunk_eq hl hml (by simpa only [msgFrame, List.append_assoc] using he)
  exact ⟨st, hw⟩

/-- **`dec.decode()`** of the reader's decoder (through the `decoder` interface), having decoded the
chain `fr` (to `s`), knowing that what it reads is a stream's bytes (`HK`): a frame of the codec from
`s`, the message decoded from it (owned, without responses), and what is known of the bytes read;
or an error (whose `Error()` returns). -/
theorem wp_stream_decode
    (hMsg : rafthttp.messageDecoder.decode.spec (GF := GF) (hG := hG))
    (hV2 : rafthttp.msgAppV2Decoder.decode.spec (GF := GF) (hG := hG))
    (N : NetPayload GF) (γw : GName) (ty : StreamTy) (lid pid : w64) (dec : GoInterface)
    (ei : GoInterfaceOk) (Hei : dec = GoInterface.ok ei) (r : GoInterface)
    (Rd B : List w8 → IProp GF) (fr : List (MsgWire × List w8)) (s : (ty.codec pid lid).S)
    (Hfr : Chain (ty.codec pid lid) (ty.codec pid lid).init fr s) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        decOwn lid pid ty dec r s ∗ readFullAt r Rd B ∗ Rd (chainBytes fr) ∗
        □ (∀ bs, B bs -∗ streamSent (ty.codec pid lid) N γw lid bs) }}
      (App (Val #(methods ei.ty go!"decode" ei.v)) (Val #()))
    {{ (ml : Loc) (err : GoInterface), RET (PairV #ml #err); http.errStrOk err ∗
        ∃ (rs' : List w8) (s' : (ty.codec pid lid).S), Rd rs' ∗ decOwn lid pid ty dec r s' ∗
          (⌜err = GoInterface.nil⌝ -∗ ∃ (w : MsgWire) (bs : List w8) (st : MsgSt),
            ⌜(ty.codec pid lid).F s w bs s' ∧ rs' = chainBytes fr ++ bs ∧ wireOf st = w ∧
              st.resps = []⌝ ∗ □ B rs' ∗ msgPtsC ml (DFrac.own 1) (DFrac.own 1) true st) }} := by
  cases ty with
  | msgAppV2 =>
    simp only [decOwn, StreamTy.codec] at Hfr ⊢
    iintro %Φ ⟨#Hpkg, Hdec, #Hrf, HRd, #HK⟩ HΦ
    icases Hdec with ⟨%d, %Hd, Hdec⟩
    subst Hd
    cases Hei
    (try wp_auto)
    wp_apply hV2 d r pid lid s Rd B (chainBytes fr) $$ [Hdec HRd]
      as %ml %err ⟨#Herr, %rs', %s', HRd, Hdec, Hok⟩
    · iframe; iframe #
      iintro !> %ys HB
      ihave Hs := HK $$ HB
      iapply streamSent_v2Compat N γw pid lid fr s ys Hfr $$ Hs
    iapply HΦ
    iframe Herr
    iexists rs', s'
    iframe HRd
    isplitl [Hdec]
    · iexists d
      iframe
      ipureintro; rfl
    simp only [v2Codec]
    iexact Hok
  | message =>
    simp only [decOwn, StreamTy.codec] at Hfr ⊢
    iintro %Φ ⟨#Hpkg, Hdec, #Hrf, HRd, #HK⟩ HΦ
    icases Hdec with ⟨%d, %Hd, #Hdr⟩
    subst Hd
    cases Hei
    (try wp_auto)
    wp_apply hMsg d r Rd B (chainBytes fr) $$ [HRd]
      as %ml %err ⟨#Herr, %rs', HRd, Hok⟩
    · iframe; iframe #
      iintro !> %bs HB
      ihave Hs := HK $$ HB
      iapply streamSent_msgFrame N γw lid fr s bs Hfr $$ Hs
    iapply HΦ
    iframe Herr
    iexists rs', ()
    iframe HRd
    isplitl []
    · iexists d
      iframe #
      ipureintro; rfl
    iintro %Hnil
    ihave ⟨%bs, %st, %Hb, #HB, Hm⟩ := Hok $$ %Hnil
    iexists (wireOf st), msgFrame bs, st
    iframe HB Hm
    ipureintro
    have hl : bs.length < 2 ^ 63 := by have := Hb.2.1; omega
    exact ⟨MsgFrameOf.of_wire Hb.2.2 hl, Hb.1, rfl, Hb.2.2.1⟩

/-- The reader's decoder is an interface value (`dec.decode` resolves its method). -/
theorem decOwn_ok (lid pid : w64) (ty : StreamTy) (dec r : GoInterface) (s : (ty.codec pid lid).S) :
    decOwn (GF := GF) lid pid ty dec r s ⊢
      decOwn lid pid ty dec r s ∗ ⌜∃ ei, dec = GoInterface.ok ei⌝ := by
  cases ty <;>
  · simp only [decOwn]
    iintro ⟨%d, %Hd, H⟩
    isplitl [H]
    · iexists d
      iframe
      ipureintro; exact Hd
    ipureintro
    exact ⟨_, Hd⟩

end lemmas

section bag
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]
open Iris.ProgramLogic Iris.Std OFE

/-- **A non-blocking send on a bag channel** (`select` with a `default`): if it goes through, the
value with its `P`; a Perennial gap (its bag idiom has the blocking send only,
`notes/perennial-changes.md`), as `bag_send_au` without the waiting case. -/
theorem bag_nonblocking_send_au (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (v : V)
    (Φ : IProp GF) :
    ⊢ £ 1 -∗ isChanBag γ ch P -∗ P v -∗ ▷ Φ -∗ nonblockingSendAuInner γ v Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef nonblockingSendAuInner
  iintro Hlc1 ⟨#Hch, #Hinv⟩ HP HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold chanBagInv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hoc0
  rcases s with buff | _ | _ | _ | _ | _ | _
  all_goals dsimp only
  case Buffered =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Hi HP] with -
    · inext; iexists .Buffered (buff ++ [v])
      dsimp only
      iframe Hoc
      iapply BigSepL.bigSepL_append.2
      iframe Hi
      iapply BigSepL.bigSepL_singleton.2
      iexact HP
    imodintro
    iexact HΦ
  case RcvPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HP] with -
    · inext; iexists .SndCommit v; iframe
    imodintro
    iexact HΦ
  all_goals first | itrivial | (iexfalso; iexact Hi)

end bag

end EtcdGrove
end Perennial
