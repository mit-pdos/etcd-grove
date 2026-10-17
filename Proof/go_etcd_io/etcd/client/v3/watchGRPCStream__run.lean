/-
Proof of `Spec/go_etcd_io/etcd/client/v3/watchGRPCStream__run.lean` (the watch slice's unit W-C).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__run
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__newWatchClient
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__nextResume
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__dispatchEvent
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__addSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__closeSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__joinSubstreams
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__serveSubstream
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__newWatcherStreamBufLogger
public import Spec.go_etcd_io.etcd.client.v3.watchRequest__toPB
public import Spec.go_etcd_io.etcd.client.v3.watcher__closeStream
public import Spec.go_etcd_io.etcd.client.v3.isHaltErr
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Error
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__enqueueCreateReq
public import Spec.go_etcd_io.etcd.client.v3.watchGRPCStream__enqueueBestEffortReq
public import Perennial.Proof.time
public import Proof.go_etcd_io.etcd.client.v3.WatchClientModel
public import Proof.go_etcd_io.etcd.client.v3.WatchContent
public import Proof.go_etcd_io.etcd.client.v3.WatchApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client


namespace client
section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The answer of the request at up position `i` (the server's token, held by `run`). -/
def ansH (γs : StreamNames) (i : Nat) : IProp GF :=
  iprop(∃ (γo : mvcc.WsStreamNames) (γa : GName),
    streamAuxIs γs (v3rpc.auxOf γo γa) ∗ v3rpc.ansTok γa i)

/-- The token of the registered watch id `X` (the server's, held by `run`). -/
def idH (γs : StreamNames) (X : w64) : IProp GF :=
  iprop(∃ (γo : mvcc.WsStreamNames) (γa : GName),
    streamAuxIs γs (v3rpc.auxOf γo γa) ∗ mvcc.idTok γo X)

/-- What `run` keeps of a received response (persistent): an mvcc response's facts. -/
def respInfo (m : v3rpc.WatchRespM) : IProp GF :=
  match m.src with
  | some ρ => mvcc.respOk ρ
  | none => iprop(True)

instance respInfo_persistent (m : v3rpc.WatchRespM) : Persistent (respInfo (GF := GF) m) := by
  unfold respInfo; split <;> infer_instance

/-- The create request of a watch. -/
abbrev createOfP (P : WsPrm GF) : v3rpc.CreateReqM := createOf P.key P.ed P.rev P.pn

/-- **A registered substream's watcher** (persistent): the mvcc watcher `w` the server registered
for its create at the id `X` (range `rg`, no filters, first revision `lo`), the id assigned to it. -/
def regFacts (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (X : w64) (w : Loc)
    (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat) : IProp GF :=
  iprop(⌜v3rpc.createRangeOk (createOfP P) X rg⌝ ∗ mvcc.watcherIs V.R.γ w rg fcs lo ∗
    fcs ↦*□ ([] : List GoFunc) ∗
    ∃ (γo : mvcc.WsStreamNames) (γa : GName), streamAuxIs γs (v3rpc.auxOf γo γa) ∗
      mvcc.idAssigned γo X w)

instance regFacts_persistent (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (X : w64) (w : Loc)
    (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat) :
    Persistent (regFacts V γs P X w rg fcs lo) := by
  unfold regFacts; infer_instance

/-- The events of the watcher `w` received so far (`Dm`), in order. -/
abbrev evsSoFar (Dm : List v3rpc.WatchRespM) (w : Loc) : List mvcc.EvM :=
  ((v3rpc.sentEvsOf Dm w).map mvcc.RespM.evs).flatten

/-- **The dispatch cursor** `hi` of a registered substream (persistent): the last event's revision
dispatched so far (`rev - 1` if none), the events so far a cut of the watcher's events of a
sealed log. -/
def cursorOk (V : WEnv GF) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM) (w : Loc)
    (rg : mvcc.WatchRange) (lo : Nat) (hi : w64) : IProp GF :=
  iprop(⌜(evsSoFar Dm w = [] ∧ hi = P.rev - W64 1) ∨
      (∃ e, (evsSoFar Dm w).getLast? = some e ∧ hi = e.kv.modRev)⌝ ∗
    (⌜evsSoFar Dm w = []⌝ ∨ ∃ (L1 : mvcc.Log) (d1 : Nat), mvcc.idxSealed V.R.γ.st.idx L1 ∗
      ⌜evsSoFar Dm w = mvcc.watchEvents L1 rg lo d1 ∧ lo ≤ d1 ∧ d1 ≤ L1.length⌝))

instance cursorOk_persistent (V : WEnv GF) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM) (w : Loc)
    (rg : mvcc.WatchRange) (lo : Nat) (hi : w64) : Persistent (cursorOk V P Dm w rg lo hi) := by
  unfold cursorOk; infer_instance

/-- **What `run` holds of a substream in its phase** (but its id field). -/
def wsRest (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM) (P : WsPrm GF) :
    WPh → IProp GF
  | .queued si => iprop(spscProducer P.γr ([] : List Loc) ∗
      monoListAuthOwn P.γhi 1 [P.rev - W64 1] ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} P.rev ∗
      (match si with
       | some i => v3rpc.upAtW γs i (.create (createOfP P))
       | none => iprop(True)))
  | .reg X => iprop(∃ (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
      (sent : List Loc) (C : List w64),
      regFacts V γs P X w rg fcs lo ∗ spscProducer P.γr sent ∗ monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ ∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P Dm w rg lo hi))
  | _ => iprop(True)

/-- **A substream `run` made and has not seen stop**: its values, its phase (agreeing with the
maps, `phOk`), its id field, what `run` holds of it. -/
def wsElem (V : WEnv GF) (γs : StreamNames) (S : RunSt) (ws : Loc) : IProp GF :=
  iprop(∃ (P : WsPrm GF) (ph : WPh), ⌜P.ws = ws ∧ phOk S ws ph⌝ ∗ wsIs V P ∗
    wsF ws go!"id" ↦ ph.id ∗ wsRest V γs S.Dm P ph)

/-- **`run`'s state at a `return`** (the deferred teardown's precondition; the local `closeErr` at
`cep`, the `closing` map at `clm`): the close error, the maps, the substreams, the wait group's
adder, `run`'s thread token, `donec` not yet closed. -/
def runExit (V : WEnv GF) (G : WgsPrm GF) (cep clm : Loc) : IProp GF :=
  iprop(∃ (γs : StreamNames) (S : RunSt) (U : GMap Loc Unit) (ce e : GoInterface) (mref : Loc)
      (s : GoSlice),
    cep ↦ ce ∗ statusErrOk ce ∗ ownMap clm (DFrac.own 1) S.CL ∗
    wgsF G.wgs go!"substreams" ↦ mref ∗ ownMap mref (DFrac.own 1) S.M ∗
    wgsF G.wgs go!"resuming" ↦ s ∗ sliceOwn s S.l ∗
    wgsF G.wgs go!"closeErr" ↦ e ∗ statusErrOk e ∗ ⌜gOk S U⌝ ∗
    ghostMapAuth G.γws 1 U ∗ ([∗map] ws ↦ _u ∈ U, wsElem V γs S ws) ∗
    wgAdder G.wgs ∗ threadTok ∗ ownBroadcastChan G.donec G.γdone (closeErrPub G.wgs) .Pending)

/-- **`run`'s state at the head of its loop** (but its local variables): the maps, the gRPC
stream's sender token and `respc`'s consumer side, what it knows (`S`, `gOk`), the server's tokens
it holds, the substreams it made (`U`), the wait group's adder, its thread token, `donec`. -/
def runCore (V : WEnv GF) (G : WgsPrm GF) (γs : StreamNames) (γr : SpscNames) (clm csm : Loc) :
    IProp GF :=
  iprop(∃ (S : RunSt) (U : GMap Loc Unit) (rcv : List Loc) (mref : Loc) (s : GoSlice)
      (e : GoInterface),
    ownMap clm (DFrac.own 1) S.CL ∗ ownMap csm (DFrac.own 1) S.CS ∗
    wgsF G.wgs go!"substreams" ↦ mref ∗ ownMap mref (DFrac.own 1) S.M ∗
    wgsF G.wgs go!"resuming" ↦ s ∗ sliceOwn s S.l ∗
    wgsF G.wgs go!"closeErr" ↦ e ∗ statusErrOk e ∗
    cliSendTok (Req := v3rpc.pbWatchRequest) γs S.L ∗ spscConsumer γr rcv ∗
    ⌜rcv.length = S.Dm.length⌝ ∗ v3rpc.downLbW γs S.Dm ∗ ⌜gOk S U⌝ ∗
    ([∗list] i ∈ S.ansd, ansH γs i) ∗ ([∗list] X ∈ S.regs, idH γs X) ∗
    (□ [∗list] m ∈ S.Dm, respInfo m) ∗
    ghostMapAuth G.γws 1 U ∗ ([∗map] ws ↦ _u ∈ U, wsElem V γs S ws) ∗
    wgAdder G.wgs ∗ threadTok ∗ ownBroadcastChan G.donec G.γdone (closeErrPub G.wgs) .Pending)

theorem runExit_of_core (V : WEnv GF) (G : WgsPrm GF) (γs : StreamNames) (γr : SpscNames)
    (clm csm cep : Loc) (ce : GoInterface) :
    runCore V G γs γr clm csm ∗ cep ↦ ce ∗ statusErrOk ce ⊢ runExit V G cep clm := by
  iintro ⟨Hc, Hcep, #Hce⟩
  unfold runCore
  icases Hc with ⟨%S, %U, %rcv, %mref, %s, %e, Hclm, -, Hsub, Hm, Hres, Hs, HcF, #He, -, -, -,
    -, %HgOk, -, -, -, Hwsa, Hels, Had, Htt, Hdn⟩
  unfold runExit
  iexists γs, S, U, ce, e, mref, s
  iframe
  iframe #
  ipureintro; exact HgOk

theorem wsElem_mono (V : WEnv GF) (γs : StreamNames) {S S' : RunSt} (ws : Loc)
    (hD : S'.Dm = S.Dm) (h : ∀ ph, phOk S ws ph → phOk S' ws ph) :
    wsElem V γs S ws ⊢ wsElem V γs S' ws := by
  unfold wsElem
  iintro ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest⟩
  iexists P, ph
  rw [hD]
  iframe HP Hid Hrest
  ipureintro; exact ⟨HPws, h ph Hph⟩

/-- **A cancel request `run` builds** (`&pb.WatchRequest{RequestUnion:
&pb.WatchRequest_CancelRequest{CancelRequest: &pb.WatchCancelRequest{WatchId: X}}}`), persisted. -/
theorem cancelReq_send (a b c : Loc) (X : w64)
    (s1 s3 : google_golang_org.protobuf.internal.impl.MessageState) (u1 u3 : GoSlice) (z1 z3 : w32) :
    a ↦ ({ state' := s1, WatchId' := X, unknownFields' := u1, sizeCache' := z1 } :
        etcdserverpb.WatchCancelRequest) ∗
      b ↦ ({ CancelRequest' := a } : etcdserverpb.WatchRequest_CancelRequest) ∗
      c ↦ ({ state' := s3,
             RequestUnion' :=
               interface.mkOk (go.GoType.PointerType etcdserverpb.WatchRequest_CancelRequest.ty) #b,
             unknownFields' := u3, sizeCache' := z3 } : etcdserverpb.WatchRequest) ⊢
    |==> v3rpc.watchReqSend (GF := GF) c (.cancel X) := by
  iintro ⟨Ha, Hb, Hc⟩
  ihave %Hann := typedPointsto_not_null _ _ _ $$ Ha
  iStructNamed Ha
  iStructNamed Hb
  iStructNamed Hc
  ipersist WatchId; ipersist CancelRequest; ipersist RequestUnion
  imodintro
  unfold v3rpc.watchReqSend v3rpc.oneofCancel
  iexists _
  iframe RequestUnion
  iexists a
  isplitr
  · ipureintro; exact Hann
  isplitl []
  · iexists b
    isplitr
    · ipureintro; rfl
    iexact CancelRequest
  iexact WatchId

/-- A points-to, split in halves. -/
theorem ptsto_split_half (l : Loc) (v : w64) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊢
      typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) ∗
        typedPointsto (GF := GF) l v (DFrac.own (1 : Qp).half) := by
  have h := ((fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)).fractional
    (1 : Qp).half (1 : Qp).half)
  rw [Qp.half_add_half] at h
  exact h.1

/-- A wholly owned `int64` cell has no other points-to. -/
theorem w64_ptsto_excl' (l : Loc) (v1 v2 : w64) (dq : DFrac) :
    (l ↦{DFrac.own 1} v1 : IProp GF) ∗ l ↦{dq} v2 ⊢ False := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  rw [typedPointstoDef_heap, typedPointstoDef_heap]
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  icombine H1 H2 gives %Hv
  exfalso
  have := DFrac.valid_own_op Hv.1
  simp at this

/-- A fresh substream (its id field owned) is none of those `run` made. -/
theorem wsElems_fresh (V : WEnv GF) (γs : StreamNames) (S : RunSt) (U : GMap Loc Unit) (ws : Loc)
    (v : w64) :
    ([∗map] w ↦ _u ∈ U, wsElem V γs S w) ∗ wsF ws go!"id" ↦ v ⊢
      ⌜U !! ws = none⌝ ∗ ([∗map] w ↦ _u ∈ U, wsElem V γs S w) ∗ wsF ws go!"id" ↦ v := by
  iintro ⟨Hm, Hid⟩
  cases h : U !! ws with
  | none => iframe; ipureintro; rfl
  | some u =>
    icases (BigSepM.bigSepM_lookup_acc h).1 $$ Hm with ⟨Hw, -⟩
    unfold wsElem
    icases Hw with ⟨%P, %ph, ⟨%HP, -⟩, -, Hid2, -⟩
    subst HP
    iexfalso
    iapply w64_ptsto_excl' $$ [$Hid $Hid2]

theorem prefix_snoc_eq {α : Type} {D L : List α} {m : α}
    (h : D <+: L ++ [m] ∨ L ++ [m] <+: D) (hl : L.length = D.length) : L = D := by
  rcases h with h | h
  · rw [List.prefix_iff_eq_take] at h
    rw [h, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  · have := h.length_le; simp at this; omega

theorem evsSoFar_snoc_ctrl (Dm : List v3rpc.WatchRespM) (m : v3rpc.WatchRespM) (w : Loc)
    (h : m.src = none) : evsSoFar (Dm ++ [m]) w = evsSoFar Dm w := by
  unfold evsSoFar
  rw [sentEvsOf_snoc, h]; simp

theorem wsRest_snoc_ctrl (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (P : WsPrm GF) (ph : WPh) (h : m.src = none) :
    wsRest V γs (Dm ++ [m]) P ph = wsRest V γs Dm P ph := by
  cases ph with
  | reg X =>
    simp only [wsRest]
    congr 1; funext w; congr 1; funext rg; congr 1; funext fcs; congr 1; funext lo
    congr 1; funext sent; congr 1; funext C
    unfold cursorOk
    rw [evsSoFar_snoc_ctrl Dm m w h]
  | queued si => rfl
  | closedRun X => rfl
  | orphan => rfl

theorem wsElem_mono' (V : WEnv GF) (γs : StreamNames) {S S' : RunSt} (ws : Loc)
    (hD : ∀ P ph, phOk S ws ph → wsRest V γs S'.Dm P ph = wsRest V γs S.Dm P ph)
    (h : ∀ ph, phOk S ws ph → phOk S' ws ph) :
    wsElem V γs S ws ⊢ wsElem V γs S' ws := by
  unfold wsElem
  iintro ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest⟩
  iexists P, ph
  rw [hD P ph Hph]
  iframe HP Hid Hrest
  ipureintro; exact ⟨HPws, h ph Hph⟩

theorem sendTok_lookup (γs : StreamNames) (L : List v3rpc.WatchReqM) (i : Nat) (r : v3rpc.WatchReqM) :
    cliSendTok (GF := GF) (Req := v3rpc.pbWatchRequest) γs L ∗ v3rpc.upAtW γs i r ⊢
      cliSendTok (Req := v3rpc.pbWatchRequest) γs L ∗ ⌜L[i]? = some r⌝ := by
  iintro ⟨Ht, #Hu⟩
  unfold cliSendTok v3rpc.upAtW
  ihave %H := mono_list_auth_idx_lookup _ _ _ _ _ $$ Ht Hu
  iframe
  ipureintro; exact H

theorem ans_fresh (γs : StreamNames) (ansd : List Nat) (i : Nat) (γo : mvcc.WsStreamNames)
    (γa : GName) :
    ([∗list] j ∈ ansd, ansH (GF := GF) γs j) ∗ streamAuxIs γs (v3rpc.auxOf γo γa) ∗
      v3rpc.ansTok γa i ⊢
      ⌜i ∉ ansd⌝ ∗ ([∗list] j ∈ ansd, ansH γs j) ∗ v3rpc.ansTok γa i := by
  iintro ⟨Hl, #Hax, Ht⟩
  by_cases hi : i ∈ ansd
  · icases BigSepL.bigSepL_mem_acc hi $$ Hl with ⟨H, -⟩
    unfold ansH
    icases H with ⟨%γo', %γa', #Hax', Ht'⟩
    ihave %He : iprop(⌜v3rpc.auxOf γo γa = v3rpc.auxOf γo' γa'⌝) $$ []
    · iapply streamAuxIs_agree
      isplit
      · iexact Hax
      · iexact Hax'
    obtain ⟨-, rfl⟩ := v3rpc.auxOf_inj He
    iexfalso
    iapply v3rpc.ansTok_excl $$ [$Ht $Ht']
  · iframe; ipureintro; exact hi

theorem id_fresh (γs : StreamNames) (regs : List w64) (X : w64) (γo : mvcc.WsStreamNames)
    (γa : GName) :
    ([∗list] Y ∈ regs, idH (GF := GF) γs Y) ∗ streamAuxIs γs (v3rpc.auxOf γo γa) ∗
      mvcc.idTok γo X ⊢
      ⌜X ∉ regs⌝ ∗ ([∗list] Y ∈ regs, idH γs Y) ∗ mvcc.idTok γo X := by
  iintro ⟨Hl, #Hax, Ht⟩
  by_cases hi : X ∈ regs
  · icases BigSepL.bigSepL_mem_acc hi $$ Hl with ⟨H, -⟩
    unfold idH
    icases H with ⟨%γo', %γa', #Hax', Ht'⟩
    ihave %He : iprop(⌜v3rpc.auxOf γo γa = v3rpc.auxOf γo' γa'⌝) $$ []
    · iapply streamAuxIs_agree
      isplit
      · iexact Hax
      · iexact Hax'
    obtain ⟨rfl, -⟩ := v3rpc.auxOf_inj He
    iexfalso
    iapply mvcc.idTok_excl $$ [$Ht $Ht']
  · iframe; ipureintro; exact hi

/-- An event response of another watcher leaves a registered substream's cursor alone. -/
theorem wsRest_snoc_other (V : WEnv GF) (γs : StreamNames) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (ρ : mvcc.RespM) (P : WsPrm GF) (X : w64) (hsrc : m.src = some ρ)
    (hX : ρ.id ≠ X) :
    mvcc.respOk ρ ∗ wsRest V γs Dm P (.reg X) ⊢ wsRest V γs (Dm ++ [m]) P (.reg X) := by
  iintro ⟨#Hr, H⟩
  simp only [wsRest]
  icases H with ⟨%w, %rg, %fcs, %lo, %sent, %C, #Hrf, Hprod, Hauth, Hrest⟩
  ihave %Hne : ⌜ρ.w ≠ w ∨ ρ.evs = []⌝ $$ []
  · unfold mvcc.respOk
    icases Hr with ⟨-, %rr, %fcs', #Hf, %Hid⟩
    unfold regFacts mvcc.watcherIs
    icases Hrf with ⟨%Hcr, ⟨%γw, %C', -, #Hf', -⟩, -⟩
    by_cases hw : ρ.w = w
    · subst hw
      ihave %Hag : iprop(⌜rr = rg ∧ fcs' = fcs⌝) $$ []
      · iapply mvcc.watcherFixed_agree
        isplit
        · iexact Hf
        · iexact Hf'
      obtain ⟨rfl, -⟩ := Hag
      ipureintro
      right
      refine Classical.byContradiction fun hn => hX ?_
      rw [Hid hn]; exact Hcr.2.2.1
    · ipureintro; left; exact hw
  have hev : evsSoFar (Dm ++ [m]) w = evsSoFar Dm w := by
    unfold evsSoFar
    rw [sentEvsOf_snoc, hsrc]
    rcases Hne with h | h
    · simp [h]
    · simp [h]
  iexists w, rg, fcs, lo, sent, C
  iframe Hrf Hprod Hauth
  unfold cursorOk
  rw [hev]
  iexact Hrest

/-- **A substream another response's id does not name** keeps its element across the response. -/
theorem wsElem_recv_other (V : WEnv GF) (γs : StreamNames) {S S' : RunSt} (ws : Loc)
    (m : v3rpc.WatchRespM) (ρ : mvcc.RespM) (hsrc : m.src = some ρ) (hD : S'.Dm = S.Dm ++ [m])
    (hX : ∀ X, phOk S ws (.reg X) → ρ.id ≠ X) (h : ∀ ph, phOk S ws ph → phOk S' ws ph) :
    mvcc.respOk ρ ∗ wsElem V γs S ws ⊢ wsElem V γs S' ws := by
  iintro ⟨#Hr, Hw⟩
  unfold wsElem
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest⟩
  iexists P, ph
  rw [hD]
  iframe HP Hid
  isplitr
  · ipureintro; exact ⟨HPws, h ph Hph⟩
  cases ph with
  | reg X =>
    iapply wsRest_snoc_other V γs S.Dm m ρ P X hsrc (hX X Hph)
    iframe Hrest; iexact Hr
  | queued si => iunfold wsRest at Hrest; simp only [wsRest]; iexact Hrest
  | closedRun X => simp only [wsRest]; itrivial
  | orphan => simp only [wsRest]; itrivial

/-- **The `k`-th response to a substream** (`k ≠ 0`, not its creation's): an mvcc response's
`WatchResponse` at `wr`, its events `es` between the cursors `hiB` and `hiA`. -/
theorem recvElem_of (V : WEnv GF) (P : WsPrm GF) (k : Nat) (hk : k ≠ 0) (m : v3rpc.WatchRespM)
    (h : Loc) (sl : GoSlice) (es : List EvModel) (hiB hiA : w64) (wr : Loc)
    (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = false) (hhn : h ≠ null) :
    wr ↦□ wrOf m h sl ∗ eventsAt sl es ∗
      watchHdrOwn h ⟨es, W64 0, false, false, m.hdr.revision⟩ ∗
      monoListIdxOwn P.γhi k hiB ∗ monoListIdxOwn P.γhi (k + 1) hiA ∗
      rangeWatchRespOk (EM := V.EM) V.pfx P.o P.rev hiB hiA ⟨es, W64 0, false, false, m.hdr.revision⟩ ⊢
    recvElem V P k wr := by
  iintro ⟨#Hwr, #Hes, Hwo, #Hi0, #Hi1, #Hrok⟩
  unfold recvElem
  ileft
  iexists wrOf m h sl, ⟨es, W64 0, false, false, m.hdr.revision⟩, hiB, hiA
  simp only [wrOf, Int.toNat_natCast, Int.natCast_eq_zero, hk, ↓reduceIte]
  iframe Hwr Hes Hwo Hi0 Hi1 Hrok
  ipureintro
  obtain ⟨h1, h2, h3⟩ := hfl
  simp [hhn, h1, h2, h3]

/-- **Before dispatching an mvcc response to its registered substream** (id `ρ.id`, watcher `w`,
`recvc` producer at `sent`, cursors `C`): the response's events, the header for `dispatchEvent`,
the content of the response for the substream (`recvElem`), the cursors extended by the new one
and the substream's state after it (the stop flag, or the cursor of the events received with this
response). -/
theorem reg_pre (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM)
    (j : Nat) (m : v3rpc.WatchRespM) (ρ : mvcc.RespM) (rs : List mvcc.RespM) (w : Loc)
    (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat) (sent : List Loc) (C : List w64)
    (h : Loc) (sl : GoSlice) (ps : List Loc) (kvs : List Loc)
    (hsrc : m.src = some ρ) (hev : m.evs = ρ.evs)
    (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = false)
    (hfilt : ρ.evs ≠ [] → v3rpc.sentEvsOf Dm ρ.w ++ [ρ] = rs.filter (fun x => decide (x.evs ≠ [])))
    (hps : ps.length = ρ.evs.length) (hkvl : kvs.length = ρ.evs.length)
    (hok : wsReqOk V.pfx P) (hpfx : V.pfx ≠ []) (hst : V.R.γ.st = V.R.E.γ) (hhn : h ≠ null) :
    srvEventIdsAssigned V.R ∗ srvLogsSmall V.R ∗ srvNoDupKeys V.R ∗
      v3rpc.mvccOk γs V.R.γ j m ∗ mvcc.watchRecvOk V.R.γ ρ.w rs ∗
      regFacts V γs P ρ.id w rg fcs lo ∗ sl ↦*□ ps ∗
      ([∗list] x ∈ ps.zip ρ.evs, mvcc.evIs (GF := GF) x.1 x.2) ∗
      eventsAt sl (List.zipWith evModelOf ρ.evs kvs) ∗
      monoListAuthOwn P.γhi 1 C ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C.length = sent.length + 1 ∧ sent ≠ []⌝ ∗ ∃ hi : w64, ⌜C.getLast? = some hi⌝ ∗
          cursorOk V P Dm w rg lo hi) ∗
      structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ m.hdr.revision ⊢
    |==> ∃ (es : List EvModel) (C' : List w64), eventsAt sl es ∗ ⌜es.length = m.evs.length⌝ ∗
      (⌜m.evs = []⌝ -∗ hdrAt h m.hdr.revision) ∗ monoListAuthOwn P.γhi 1 C' ∗
      (∀ wr : Loc, wr ↦□ wrOf m h sl -∗ recvElem V P sent.length wr) ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ ∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P (Dm ++ [m]) w rg lo hi) := by
  iintro ⟨#HS3, #Hsm, #Hnd, #Hmv, #Hrecv, #Hrf, #Hsl, #Hevs, #Hea, Hauth, Hst, Hrev⟩
  ihave Hhdr : iprop(|==> ((⌜m.evs = []⌝ ∗ hdrAt h m.hdr.revision) ∨
      (⌜m.evs ≠ []⌝ ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ m.hdr.revision)))
      $$ [Hrev]
  · by_cases hne : m.evs = []
    · ipersist Hrev
      imodintro
      ileft
      isplitr
      · ipureintro; exact hne
      unfold hdrAt; iright
      iframe Hrev
      ipureintro; exact hhn
    · imodintro
      iright
      iframe
      ipureintro; exact hne
  imod Hhdr
  icases Hst with (#Hx | ⟨⟨%Hlen, %Hsne⟩, %hi, %Hlast, #Hcur⟩)
  · -- the substream stopped: nothing to give
    imodintro
    iexists List.zipWith evModelOf ρ.evs kvs, C
    iframe Hea Hauth
    isplitr
    · ipureintro; simp [hkvl, hev]
    isplitl [Hhdr]
    · icases Hhdr with (⟨%hne, #Hha⟩ | ⟨%hne, -⟩)
      · iintro %-; iexact Hha
      · iintro %h'; exact absurd h' hne
    isplitr
    · iintro %wr -
      unfold recvElem
      iright; iexact Hx
    ileft; iexact Hx
  -- the substream runs: the response's content
  iunfold regFacts at Hrf
  icases Hrf with ⟨%Hcr, #Hwi, #Hfcs, %γo, %γa, #Hax, #Hias⟩
  ihave %hρw : ⌜ρ.evs ≠ [] → ρ.w = w⌝ $$ []
  · by_cases hne : ρ.evs = []
    · ipureintro; intro h'; exact absurd hne h'
    · iunfold srvEventIdsAssigned at HS3
      ihave ⟨%γo', %γa', #Hax', #Hias'⟩ := HS3 $$ %γs %j %m %ρ Hmv %(And.intro hsrc hne)
      ihave %He : iprop(⌜v3rpc.auxOf γo γa = v3rpc.auxOf γo' γa'⌝) $$ []
      · iapply streamAuxIs_agree
        isplit
        · iexact Hax
        · iexact Hax'
      obtain ⟨rfl, -⟩ := v3rpc.auxOf_inj He
      ihave %Hw := mvcc.idAssigned_agree γo ρ.id w ρ.w $$ [Hias Hias']
      · isplit
        · iexact Hias
        · iexact Hias'
      ipureintro; intro _; exact Hw.symm
  iunfold cursorOk at Hcur
  icases Hcur with ⟨%Hhi, #Hcut⟩
  have hfilt' : ρ.evs ≠ [] → v3rpc.sentEvsOf Dm w ++ [ρ] =
      rs.filter (fun x => decide (x.evs ≠ [])) := fun hne => by rw [← hρw hne]; exact hfilt hne
  ihave ⟨%es, #Hes, %Hesl, #Hrok, %Hhi', #Hcut'⟩ := dispatch_content V P Dm m ρ rs ρ.id w rg fcs lo
      hi sl ps m.hdr.revision hsrc hρw hfilt' hps hok hpfx hst Hcr Hhi $$ []
  · iframe #
  imod monoListAuthOwn_update_app (γ := P.γhi) (l := C)
      [(es.getLast?.map EvModel.rev).getD hi] $$ Hauth with ⟨Hauth, #Hlb⟩
  have hC0 : (C ++ [(es.getLast?.map EvModel.rev).getD hi])[sent.length]? = some hi := by
    rw [List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?] at Hlast
    rw [show sent.length = C.length - 1 by omega]; exact Hlast
  have hC1 : (C ++ [(es.getLast?.map EvModel.rev).getD hi])[sent.length + 1]? =
      some ((es.getLast?.map EvModel.rev).getD hi) := by
    rw [List.getElem?_append_right (by omega)]
    simp [Hlen]
  ihave #Hi0 := monoListIdxOwn_get (γ := P.γhi) sent.length hi hC0 $$ Hlb
  ihave #Hi1 := monoListIdxOwn_get (γ := P.γhi) (sent.length + 1) ((es.getLast?.map EvModel.rev).getD hi) hC1 $$ Hlb
  ihave ⟨Hwo, Hhw⟩ : iprop(watchHdrOwn h ⟨es, W64 0, false, false, m.hdr.revision⟩ ∗
      (⌜m.evs = []⌝ -∗ hdrAt h m.hdr.revision)) $$ [Hhdr]
  · icases Hhdr with (⟨%hne, #Hha⟩ | ⟨%hne, Hrev⟩)
    · have hes : es = [] := by
        rw [← List.length_eq_zero_iff, Hesl, ← hev, hne]; rfl
      simp only [watchHdrOwn, hes, ↓reduceIte]
      isplitl []
      · iexact Hha
      · iintro %-; iexact Hha
    · have hes : es ≠ [] := by
        intro e; apply hne; rw [← List.length_eq_zero_iff, hev, ← Hesl, e]; rfl
      simp only [watchHdrOwn, hes, ↓reduceIte]
      isplitl [Hrev]
      · iframe; ipureintro; exact hhn
      · iintro %h'; exact absurd h' hne
  imodintro
  iexists es, C ++ [(es.getLast?.map EvModel.rev).getD hi]
  iframe Hes Hhw Hauth
  isplitr
  · ipureintro; rw [Hesl, hev]
  isplitl [Hwo]
  · iintro %wr #Hwr
    iapply recvElem_of V P sent.length (by intro h0; exact Hsne (List.length_eq_zero_iff.1 h0)) m h
      sl es hi ((es.getLast?.map EvModel.rev).getD hi) wr hfl hhn
    iframe Hwr Hes Hwo Hi0 Hi1 Hrok
  iright
  isplitr
  · ipureintro; simp [Hlen]
  iexists ((es.getLast?.map EvModel.rev).getD hi)
  isplitr
  · ipureintro; simp
  unfold cursorOk
  iframe Hcut'
  ipureintro; exact Hhi'

/-- **After dispatching to a registered substream**: its state over the new response, whether
the send succeeded or failed. -/
theorem reg_post (V : WEnv GF) (γs : StreamNames) (P : WsPrm GF) (Dm : List v3rpc.WatchRespM)
    (m : v3rpc.WatchRespM) (X : w64) (w : Loc) (rg : mvcc.WatchRange) (fcs : GoSlice) (lo : Nat)
    (sent : List Loc) (C' : List w64) (b : Bool) (wr : Loc) :
    regFacts V γs P X w rg fcs lo ∗ monoListAuthOwn P.γhi 1 C' ∗
      (dghostVar P.γx DFrac.discard true ∨
        ⌜C'.length = sent.length + 2⌝ ∗ ∃ hi : w64, ⌜C'.getLast? = some hi⌝ ∗
          cursorOk V P (Dm ++ [m]) w rg lo hi) ∗
      ((⌜b = true⌝ ∗ sendDone P sent wr) ∨ (⌜b = false⌝ ∗ sendFail V P sent wr)) ⊢
    wsRest V γs (Dm ++ [m]) P (.reg X) := by
  iintro ⟨#Hrf, Hauth, Hst, Hs⟩
  simp only [wsRest]
  icases Hs with (⟨%-, Hd⟩ | ⟨%-, Hf⟩)
  · iunfold sendDone at Hd
    iexists w, rg, fcs, lo, sent ++ [wr], C'
    iframe Hrf Hd Hauth
    icases Hst with (#Hx | ⟨%Hlen, %hi, %Hl, #Hc⟩)
    · ileft; iexact Hx
    · iright
      isplitr
      · ipureintro; simp [Hlen]
      iexists hi
      iframe Hc
      ipureintro; exact Hl
  · iunfold sendFail at Hf
    icases Hf with ⟨Hp, -, #Hx⟩
    iexists w, rg, fcs, lo, sent, C'
    iframe Hrf Hp Hauth
    ileft; iexact Hx

/-- **An id in `substreams`** is registered and not `-1` (its substream's phase says so). -/
theorem M_entry_facts (V : WEnv GF) (γs : StreamNames) {S : RunSt} {U : GMap Loc Unit} {X : w64}
    {ws : Loc} (hg : gOk S U) (hM : S.M !! X = some ws) :
    ([∗map] ws' ↦ _u ∈ U, wsElem V γs S ws') ⊢
      ⌜X ∈ S.regs ∧ X ≠ W64 (-1)⌝ ∗ ([∗map] ws' ↦ _u ∈ U, wsElem V γs S ws') := by
  iintro Hels
  have hU : U !! ws = some () := hg.1 X ws hM
  icases (BigSepM.bigSepM_delete hU).1 $$ Hels with ⟨Hw, Hels⟩
  iunfold wsElem at Hw
  icases Hw with ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest⟩
  have Hf : X ∈ S.regs ∧ X ≠ W64 (-1) := by
    cases ph with
    | queued si => exact absurd hM (Hph.1 X)
    | orphan => exact absurd hM (Hph.1 X)
    | reg Y =>
      have := hg.2.1 X Y ws hM Hph.1; subst this; exact ⟨Hph.2.2.2.1, Hph.2.2.2.2.1⟩
    | closedRun Y => exact absurd hM (Hph.1.2.1 X)
  isplitr
  · ipureintro; exact Hf
  iapply (BigSepM.bigSepM_delete hU).2
  iframe Hels
  unfold wsElem
  iexists P, ph
  iframe HP Hid Hrest
  ipureintro; exact ⟨HPws, Hph⟩

/-- **A new watcher's events so far are none**: an mvcc response with events of the watcher `w`
(range `rg`, of the id `X`) received before would name the id `X`, registered by then. -/
theorem evsSoFar_fresh {S : RunSt} {U : GMap Loc Unit} (X : w64) (w : Loc) (rg : mvcc.WatchRange)
    (fcs : GoSlice) (hg : gOk S U) (hX : X ∉ S.regs) (hrg : rg.id = X) :
    (□ [∗list] m ∈ S.Dm, respInfo (GF := GF) m) ∗ mvcc.watcherFixed w rg fcs ⊢
      ⌜evsSoFar S.Dm w = []⌝ := by
  iintro ⟨#Hinfo, #Hf⟩
  by_cases hc : v3rpc.sentEvsOf S.Dm w = []
  · ipureintro; unfold evsSoFar; rw [hc]; rfl
  iexfalso
  obtain ⟨ρ, hρ⟩ := List.exists_mem_of_ne_nil _ hc
  unfold v3rpc.sentEvsOf at hρ
  simp only [List.mem_filter, decide_eq_true_eq] at hρ
  obtain ⟨hρm, hρw, hρe⟩ := hρ
  obtain ⟨m', hm', hsrc'⟩ := List.mem_filterMap.1 hρm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hm'
  icases BigSepL.bigSepL_mem_acc hm' $$ Hinfo with ⟨#Hi, -⟩
  irevert Hi
  unfold respInfo
  rw [hsrc']
  iintro #Hr
  iunfold mvcc.respOk at Hr
  icases Hr with ⟨-, %rr, %fcs', #Hf', %Hid⟩
  subst hρw
  ihave %Hag : iprop(⌜rg = rr ∧ fcs = fcs'⌝) $$ []
  · iapply mvcc.watcherFixed_agree
    isplit
    · iexact Hf
    · iexact Hf'
  obtain ⟨rfl, -⟩ := Hag
  have hid := Hid hρe
  obtain ⟨-, hl⟩ := hg.2.2.2.2.2.2.2.2.2.2.2.1 j m' ρ hj hsrc'
  obtain ⟨mc, hmc, hs, hw, hcr, hca⟩ := idLive_exists hl
  have := hg.2.2.2.2.2.2.2.2.2.2.2.2 mc (List.mem_of_mem_take hmc) hs hcr hca
  exfalso; apply hX; rw [← hrg, ← hid, ← hw]; exact this

/-- **The first response to a substream**, its creation's (no events, the cursor `hi` both
before and after, the request's `rev` field's half). -/
theorem recvElem_created (V : WEnv GF) (P : WsPrm GF) (m : v3rpc.WatchRespM) (h : Loc)
    (sl : GoSlice) (hi rv : w64) (wr : Loc)
    (hfl : m.compactRev = W64 0 ∧ m.canceled = false ∧ m.created = true) (hhn : h ≠ null) :
    wr ↦□ wrOf m h sl ∗ eventsAt sl [] ∗ hdrAt h m.hdr.revision ∗
      monoListIdxOwn P.γhi 0 hi ∗ monoListIdxOwn P.γhi 1 hi ∗
      wsReqF P.ws go!"rev" ↦{DFrac.own (1 : Qp).half} rv ⊢
    recvElem V P 0 wr := by
  iintro ⟨#Hwr, #Hes, #Hha, #Hi0, #Hi1, Hrv⟩
  unfold recvElem
  ileft
  iexists wrOf m h sl, ⟨[], W64 0, false, true, m.hdr.revision⟩, hi, hi
  simp only [wrOf, Int.toNat_zero, Nat.zero_add, ↓reduceIte]
  iframe Hwr Hes Hi0 Hi1
  obtain ⟨h1, h2, h3⟩ := hfl
  isplitr
  · ipureintro; simp [hhn, h1, h2, h3]
  isplitr
  · unfold watchHdrOwn; simp only [↓reduceIte]; iexact Hha
  isplitr
  · unfold rangeWatchRespOk
    isplitr
    · ipureintro; simp [EvRevSorted]
    imodintro
    iintro %k %e %hk
    simp at hk
  isplitr
  · ipureintro; simp
  iexists rv; iexact Hrv

/-- The ids registered after a created response: a new one unless refused. -/
theorem regs_join (γs : StreamNames) (b : Bool) (regs : List w64) (X : w64) :
    ([∗list] Y ∈ regs, idH (GF := GF) γs Y) ∗ ([∗list] Y ∈ (if b then [] else [X]), idH γs Y) ⊢
      [∗list] Y ∈ (if b then regs else regs ++ [X]), idH γs Y := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨H1, H2⟩
    iapply BigSepL.bigSepL_append.2
    iframe
  · simp only [↓reduceIte]
    iintro ⟨H1, -⟩
    iexact H1

/-- Some watch parameters (for a dispatch with no target). -/
def dummyWsPrm (G : WgsPrm GF) (γr : SpscNames) : WsPrm GF :=
  WsPrm.mk (OpFull.mk OpModel.zero (W64 0) [] false false false (W64 0) [] false (W64 0) (W64 0)
    false false) (W64 0) G.ctx G.cd [] [] false false false slice.nil null G.γreq null
    (EtcdWatchNames.mk γr G.γws) null null γr G.γws null G.γreq G.γws

/-- A substream's id field, any value (`closeSubstream`'s). -/
def idE (ws : Loc) : IProp GF := iprop(∃ id : w64, wsF ws go!"id" ↦ id)

/-- What the teardown closes of a substream in its phase: `recvc` (its producer) if `run` holds it. -/
def closerRes (V : WEnv GF) (ws : Loc) : WPh → IProp GF
  | .queued _ => recvcCloser V ws
  | .reg _ => recvcCloser V ws
  | _ => iprop(True)

/-- A substream's closer, with its phase. -/
def closerE (V : WEnv GF) (S : RunSt) (ws : Loc) : IProp GF :=
  iprop(∃ ph : WPh, ⌜phOk S ws ph⌝ ∗ closerRes V ws ph)

theorem wsElem_split (V : WEnv GF) (γs : StreamNames) (S : RunSt) (ws : Loc) :
    wsElem V γs S ws ⊢ idE ws ∗ closerE V S ws ∗ donecOf ws := by
  unfold wsElem
  iintro ⟨%P, %ph, ⟨%HPws, %Hph⟩, #HP, Hid, Hrest⟩
  subst HPws
  ihave #HP' := HP
  iunfold wsIs at HP'
  icases HP' with ⟨-, -, -, #Hdc, -, -, #Hdb, -⟩
  isplitl [Hid]
  · unfold idE; iexists _; iexact Hid
  isplitl [Hrest]
  · unfold closerE
    iexists ph
    isplitr
    · ipureintro; exact Hph
    cases ph with
    | queued si =>
      unfold wsRest closerRes recvcCloser
      icases Hrest with ⟨Hprod, -⟩
      iexists P, []
      iframe HP Hprod
      ipureintro; rfl
    | reg X =>
      unfold wsRest closerRes recvcCloser
      icases Hrest with ⟨%w, %rg, %fcs, %lo, %sent, %C, -, Hprod, -⟩
      iexists P, sent
      iframe HP Hprod
      ipureintro; rfl
    | closedRun X => unfold closerRes; itrivial
    | orphan => unfold closerRes; itrivial
  unfold donecOf
  iexists P.donec, P.γdn, _
  iframe Hdc Hdb

theorem wsElems_split (V : WEnv GF) (γs : StreamNames) (S : RunSt) (U : GMap Loc Unit) :
    ([∗map] ws ↦ _u ∈ U, wsElem V γs S ws) ⊢
      ([∗map] ws ↦ _u ∈ U, idE ws) ∗ ([∗map] ws ↦ _u ∈ U, closerE V S ws) ∗
      □ (∀ ws, ⌜U !! ws = some ()⌝ → donecOf ws) := by
  refine (BigSepM.bigSepM_mono_of_forall (fun {_ _} => wsElem_split V γs S _)).trans ?_
  rw [BigSepM.bigSepM_sep_eq, BigSepM.bigSepM_sep_eq]
  iintro ⟨Hid, Hcl, #Hdc⟩
  iframe Hid Hcl
  imodintro
  iintro %ws %Hws
  iapply (BigSepM.bigSepM_lookup (Φ := fun ws (_ : Unit) => donecOf (GF := GF) ws) Hws) $$ Hdc

/-- The teardown's closing loops' facts: the substreams still to close (`U1`), those of `U` the
closing map (`CL'`) does not hold, the original closing map within it. -/
def tdOk (S : RunSt) (U CL' U1 : GMap Loc Unit) : Prop :=
  (∀ ws, U1 !! ws = some () → U !! ws = some ()) ∧
  (∀ ws, U !! ws = some () → CL' !! ws = none → U1 !! ws = some ()) ∧
  (∀ ws, S.CL !! ws = some () → CL' !! ws = some ())

theorem tdOk_init (S : RunSt) (U : GMap Loc Unit) : tdOk S U S.CL U :=
  ⟨fun _ h => h, fun _ h _ => h, fun _ h => h⟩

theorem tdOk_close {S : RunSt} {U CL' U1 : GMap Loc Unit} (h : tdOk S U CL' U1) (ws : Loc) :
    tdOk S U (GMap.insert ws () CL') (GMap.delete ws U1) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun w hw => ?_, fun w hw hc => ?_, fun w hw => ?_⟩
  · by_cases e : ws = w
    · subst e; rw [GMap.lookup_delete] at hw; cases hw
    · rw [GMap.lookup_delete_ne _ e] at hw; exact h1 w hw
  · by_cases e : ws = w
    · subst e; rw [GMap.lookup_insert] at hc; cases hc
    · rw [GMap.lookup_insert_ne _ _ e] at hc; rw [GMap.lookup_delete_ne _ e]; exact h2 w hw hc
  · by_cases e : ws = w
    · subst e; rw [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ e]; exact h3 w hw

end defs
end client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

set_option maxRecDepth 100000 in
/-- **`run` with etcd-io/etcd#21065: unfinished** (`notes/pr-verify/etcd-21065.md`, "Why `run`'s
proof is open"). The proof on `lean` (this file there) rests on `run` holding the gRPC stream's
sender token (`cliSendTok γs S.L`): it knows the whole up queue `S.L`, so that a `Created` answering
the up position `i` (the server's answer token for `i`) is the create of the head of `resuming`
(`gOk`: every create in `S.L` is answered or the pending one, `pend = some i`). With the PR the
token is `sendLoop`'s, which sends what it takes from two queues in an order `run` does not see, and
the stream's `Send` (`cliBidiStreamIs`, a trust-boundary model) is not logically atomic: when the
server's answer for `i` reaches `run`, `sendLoop` may still be inside the `Send` that put the
request at `i`, and nothing `run` can hold then ties position `i` to a request it enqueued. Closing
the proof needs a logically atomic `Send` (the request's position fixed by an atomic update at the
linearization point), a change of the gRPC model to be designed on its own. The callees' specs are
all proved; the helper lemmas above are `lean`'s. -/
theorem watchGRPCStream.run.wp_proof
    (wp_newWC : watchGRPCStream.newWatchClient.spec (GF := GF) (hG := hG))
    (wp_nextResume : watchGRPCStream.nextResume.spec (GF := GF) (hG := hG))
    (wp_dispatch : watchGRPCStream.dispatchEvent.spec (GF := GF) (hG := hG))
    (wp_addSub : watchGRPCStream.addSubstream.spec (GF := GF) (hG := hG))
    (wp_closeSub : watchGRPCStream.closeSubstream.spec (GF := GF) (hG := hG))
    (wp_join : watchGRPCStream.joinSubstreams.spec (GF := GF) (hG := hG))
    (wp_serveSub : watchGRPCStream.serveSubstream.spec (GF := GF) (hG := hG))
    (wp_bufLogger : watchGRPCStream.newWatcherStreamBufLogger.spec (GF := GF) (hG := hG))
    (wp_toPB : watchRequest.toPB.spec (GF := GF) (hG := hG))
    (wp_closeStream : watcher.closeStream.spec (GF := GF) (hG := hG))
    (wp_isHaltErr : isHaltErr.spec (GF := GF) (hG := hG))
    (wp_Debug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (wp_zapError : zap.Error.spec (GF := GF) (hG := hG))
    (wp_enqC : watchGRPCStream.enqueueCreateReq.spec (GF := GF) (hG := hG))
    (wp_enqB : watchGRPCStream.enqueueBestEffortReq.spec (GF := GF) (hG := hG)) :
    watchGRPCStream.run.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
