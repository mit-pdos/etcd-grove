/-
**The stream reader's goroutine** (rafthttp stage 5c): what `streamReader.run`, `start`, `stop` and
`dial` share, beyond the reader's fields of `Reader.lean`. Lean-first.

* `srCfg`: the fields `dial` and `run` read and nothing writes once the reader is made: its type,
  rate limiter (`rate.limiterOk`), picker (of the peer's URLs), its transport's URLs, cluster id,
  stream round tripper (of the raft network) and `ErrorC`; the stream registry (`streamRegInv`)
  and the peer's hosts' registration (`pipeReg`).
* `srDial`: `srCfg` and the reader's `errorc`, which `start` sets.
* `srFixed0`: `srFixed` but the context, which `start` sets (`srFixed_intro`).
* `srStopRight` (persistent): the context's cancel function and the `done` channel, which `stop`
  cancels and waits for; `srDoneRight` (exclusive, `run`'s): the right to close `done`.
* `wp_Is_errStrOk`: `errors.Is(err, target)` of an `http.errStrOk` error and a pointer target
  returns (`http.errTreeOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Reader
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Sender
public import Spec.golang_org.x.time.rate.Limiter__Wait
public import Spec.errors.Is

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

/-- **The reader's configuration** (persistent) of the local member `lid`, reading the stream of
type `ty` from `pid`: its type, rate limiter, picker (of `pid`'s URLs), its transport's URLs,
cluster id, stream round tripper (of the raft network) and `ErrorC`; the stream registry and
`pid`'s hosts' registration. (What `dial` reads: stated with `dial`'s spec, before its proof,
stage 5d.) -/
def srCfg (Rh : RaftHttp GF) (pid : w64) (ty : StreamTy) (cr : Loc) : IProp GF :=
  iprop(∃ (rl pk tr : Loc) (urls : GoSlice) (uvs : List net.url.URL)
      (cid : go_etcd_io.etcd.client.pkg.v3.types.ID) (rt : GoInterface) (ec : GoChan),
    cr.[rafthttp.streamReader, go!"typ"] ↦□ ty.str ∗
    cr.[rafthttp.streamReader, go!"rl"] ↦□ rl ∗ rate.limiterOk rl ∗
    cr.[rafthttp.streamReader, go!"picker"] ↦□ pk ∗ pickerOk pk (peerURL Rh pid) ∗
    cr.[rafthttp.streamReader, go!"tr"] ↦□ tr ∗
    tr.[rafthttp.Transport, go!"URLs"] ↦□ urls ∗ urls ↦*□ uvs ∗
    tr.[rafthttp.Transport, go!"ClusterID"] ↦□ cid ∗
    tr.[rafthttp.Transport, go!"streamRt"] ↦□ rt ∗ http.roundTripperOk (raftHttpNet Rh) rt ∗
    tr.[rafthttp.Transport, go!"ErrorC"] ↦□ ec ∗
    streamRegInv Rh ∗ pipeReg Rh pid)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance srCfg_persistent (Rh : RaftHttp GF) (pid : w64) (ty : StreamTy) (cr : Loc) :
    Persistent (srCfg Rh pid ty cr) := by
  unfold srCfg; infer_instance

/-- **What `dial` reads** (persistent): the configuration and the reader's `errorc`. -/
def srDial (Rh : RaftHttp GF) (pid : w64) (ty : StreamTy) (cr : Loc) : IProp GF :=
  iprop(srCfg Rh pid ty cr ∗ ∃ ec : GoChan, cr.[rafthttp.streamReader, go!"errorc"] ↦□ ec)

instance srDial_persistent (Rh : RaftHttp GF) (pid : w64) (ty : StreamTy) (cr : Loc) :
    Persistent (srDial Rh pid ty cr) := by
  unfold srDial; infer_instance

/-- **The reader's fixed fields but its context** (persistent): `srFixed` before `start` sets
the context. -/
def srFixed0 (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (cr : Loc) : IProp GF :=
  iprop(∃ (lg tr ps : Loc) (rc pc : GoChan) (γr γp : ChanNames),
    cr.[rafthttp.streamReader, go!"lg"] ↦□ lg ∗ ⌜lg ≠ null⌝ ∗
    cr.[rafthttp.streamReader, go!"peerID"] ↦□ pid ∗
    cr.[rafthttp.streamReader, go!"tr"] ↦□ tr ∗ tr.[rafthttp.Transport, go!"ID"] ↦□ lid ∗
    cr.[rafthttp.streamReader, go!"status"] ↦□ ps ∗ peerStatusOk ps ∗
    cr.[rafthttp.streamReader, go!"recvc"] ↦□ rc ∗ isChanBag γr rc (netRecv Rh.γn lid γd) ∗
    cr.[rafthttp.streamReader, go!"propc"] ↦□ pc ∗ isChanBag γp pc (netRecv Rh.γn lid γd) ∗
    sync.isMutex (cr.[rafthttp.streamReader, go!"mu"]) (srLockInv cr))

set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 16384 in
instance srFixed0_persistent (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (cr : Loc) :
    Persistent (srFixed0 Rh lid pid γd cr) := by
  unfold srFixed0; infer_instance

/-- **The right to stop the reader** `cr` (persistent): its context's cancel function, and its
`done` channel (only closed). -/
def srStopRight (cr : Loc) : IProp GF :=
  iprop(∃ (cf : GoFunc) (γc : context.ContextNames) (dc : GoChan) (γdn : ChanNames),
    cr.[rafthttp.streamReader, go!"cancel"] ↦□ cf ∗ context.cancelSpec cf γc iprop(True) ∗
    cr.[rafthttp.streamReader, go!"done"] ↦□ dc ∗ ownBroadcastChan dc γdn iprop(True) .Unknown)

instance srStopRight_persistent (cr : Loc) : Persistent (srStopRight (GF := GF) cr) := by
  unfold srStopRight; infer_instance

/-- **The right to close the reader `cr`'s `done`** (exclusive, `run`'s): once, when it returns. -/
def srDoneRight (cr : Loc) : IProp GF :=
  iprop(∃ (dc : GoChan) (γdn : ChanNames), cr.[rafthttp.streamReader, go!"done"] ↦□ dc ∗
    ownBroadcastChan dc γdn iprop(True) .Pending)

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The reader's fixed fields, once its context is set. -/
theorem srFixed_intro (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (cr : Loc)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    ⊢ srFixed0 Rh lid pid γd cr -∗ cr.[rafthttp.streamReader, go!"ctx"] ↦□ GoInterface.ok ctx -∗
      context.isContext ctx cd -∗ srFixed Rh lid pid γd cr := by
  iintro #H0 #Hc #Hctx
  iunfold srFixed0 at H0
  icases H0 with ⟨%lg, %tr, %ps, %rc, %pc, %γr, %γp, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, #H9,
    #H10, #H11, #H12⟩
  iunfold srFixed
  iexists lg, tr, ps, rc, pc, γr, γp, ctx, cd
  iframe #

/-- **`ctx.Err()`** of a context (`isContext`'s own triple, `"#HErr"`): some error. -/
theorem wp_ctx_Err (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) :
    {{ context.isContext ctx cd }}
      (App (Val #(methods ctx.ty go!"Err" ctx.v)) (Val #()))
    {{ (err : GoInterface), RET #err; True }} := by
  iintro %Φ #Hc HΦ
  unfold context.isContext context.isContextDef
  iNamed Hc
  ihave #HE := HErr $$ %Broadcast.Unknown
  iapply HE
  · itrivial
  inext
  iintro %err -
  iapply HΦ
  itrivial

variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- **`errors.Is(err, target)`** of an error whose `Error()` returns (`http.errStrOk`, of a
well-formed error tree) and a pointer target: some `bool`. -/
theorem wp_Is_errStrOk (hIs : errors.Is.spec (GF := GF) (hG := hG)) (err target : GoInterface)
    (Htgt : ∀ tii, target = GoInterface.ok tii → _root_.Perennial.errors.IsPointerError tii) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ http.errStrOk err }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #target))
    {{ (b : Bool), RET #b; True }} := by
  iintro %Φ ⟨#Hpkg, #He⟩ HΦ
  iunfold http.errStrOk at He
  icases He with (%Hn | ⟨%ei, %Hei, -, #Htree⟩)
  · subst Hn
    wp_apply hIs (· = GoInterface.nil) (fun _ => False) GoInterface.nil target Htgt
      (fun _ _ h => by cases h) $$ [] as %b -
    · iframe #
      isplitl
      · iintro !> %ii %h
        cases h
      ipureintro; rfl
    iapply HΦ; itrivial
  · subst Hei
    iunfold http.errTreeOk at Htree
    ihave ⟨%S, %M, %HS, #Ht⟩ := Htree $$ %target %Htgt
    wp_apply hIs S M (GoInterface.ok ei) target Htgt HS.2 $$ [] as %b -
    · iframe #
      ipureintro; exact HS.1
    iapply HΦ; itrivial

end lemmas

end EtcdGrove
end Perennial
