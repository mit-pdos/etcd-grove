/-
**`Transport.Handler`** (rafthttp stage 6c; restated over the transport's state in 6d): the mux of
the pipeline, stream, snapshot and prober handlers, a handler of the member's address for the raft
protocol, lending each invocation an `R` (its `Process`) and a reader's token of the transport's
lock (its `Get`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportInv
public import Proof.net.http.Axioms
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newPipelineHandler
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newStreamHandler
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newSnapshotHandler
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Get
public import Spec.github_com.xiang90.probing.NewHandler
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipelineHandler__ServeHTTP
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamHandler__ServeHTTP

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

/-! ## Routing -/

/-- The pattern a path is routed to matches it. -/
theorem http.route_matches (pats : List GoString) (p pat : GoString)
    (h : http.route pats p = some pat) : http.patMatches pat p = true := by
  unfold http.route at h
  suffices H : ∀ (l : List GoString) (acc : Option GoString),
      (∀ x, acc = some x → http.patMatches x p = true) →
      (∀ x ∈ l, http.patMatches x p = true) →
      ∀ x, l.foldl (fun best q => match best with
        | none => some q
        | some b => if b.length < q.length then some q else some b) acc = some x →
        http.patMatches x p = true by
    exact H _ none (by simp) (fun x hx => (List.mem_filter.1 hx).2) pat h
  intro l
  induction l with
  | nil => intro acc hacc _ x hx; exact hacc x hx
  | cons q l ih =>
    intro acc hacc hl x hx
    simp only [List.foldl_cons] at hx
    refine ih _ ?_ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x hx
    intro y hy
    cases acc with
    | none => simp at hy; subst hy; exact hl q (List.mem_cons_self ..)
    | some b =>
      simp only at hy
      split at hy
      · simp at hy; subst hy; exact hl q (List.mem_cons_self ..)
      · simp at hy; subst hy; exact hacc b rfl

/-- A path routed to `/raft` is `/raft`. -/
theorem http.route_raft (pats : List GoString) (p : GoString)
    (h : http.route pats p = some go!"/raft") : p = go!"/raft" := by
  have := http.route_matches _ _ _ h
  simp [http.patMatches] at this
  exact this.symm

/-- A path routed to the prober's is the prober's. -/
theorem http.route_probing (pats : List GoString) (p : GoString)
    (h : http.route pats p = some probingPath) : p = probingPath := by
  have := http.route_matches _ _ _ h
  simp [http.patMatches, probingPath] at this
  exact this.symm

/-- A path routed to the stream prefix is not the prober's. -/
theorem http.route_stream (pats : List GoString) (p : GoString)
    (h : http.route pats p = some go!"/raft/stream/") : p ≠ probingPath := by
  have := http.route_matches _ _ _ h
  intro hp
  subst hp
  revert this
  decide

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

/-- **`addRemoteFromRequest` of the transport `t` returns** (persistent; the handlers' premise,
which 6d proves of the transport's state: in a static cluster, the request's sender is a peer). -/
def trAddRemoteReq (t : Loc) : IProp GF :=
  iprop(□ ∀ (r : Loc) (R' : http.HReq) (rd : GoInterface),
    {{ http.reqAt r R' rd }}
      (App (App (Val (@! rafthttp.addRemoteFromRequest))
        (Val #(interface.mkOk (go.GoType.PointerType rafthttp.Transport.ty) #t))) (Val #r))
    {{ RET #(); True }})

instance trAddRemoteReq_persistent (t : Loc) : Persistent (trAddRemoteReq (GF := GF) t) := by
  unfold trAddRemoteReq; infer_instance

/-- **`AddRemote` of the transport `t` returns** (persistent; the stream handler's premise, as
`trAddRemoteReq`). -/
def trAddRemote (t : Loc) : IProp GF :=
  iprop(□ ∀ (pid : w64) (sl : GoSlice) (us : List GoString), {{ sl ↦* us }}
    (App (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"AddRemote"))
      (Val #pid)) (Val #sl))
    {{ RET #(); True }})

instance trAddRemote_persistent (t : Loc) : Persistent (trAddRemote (GF := GF) t) := by
  unfold trAddRemote; infer_instance

/-- A raft of `netRaftOk` borrowing `R` borrows `R ∗ T` too. -/
theorem netRaftOk_frame (γn : NetNames GF) (id : w64) (γd : GName) (R T : IProp GF)
    (r : GoInterface) : netRaftOk γn id γd R r ⊢ netRaftOk γn id γd iprop(R ∗ T) r := by
  iintro #H
  iunfold netRaftOk at H
  icases H with ⟨%ri, %Hri, #HP, #HI, #HU, #HS⟩
  iunfold netRaftOk
  iexists ri
  iframe #
  isplitr
  · ipureintro; exact Hri
  iintro !> %ctx %cd %ml %Φ !> ⟨Hc, ⟨HR, HT⟩, Hrv⟩ HΦ
  iapply HP $$ [$Hc $HR $Hrv]
  inext
  iintro %err ⟨He, HR⟩
  iapply HΦ
  iframe

/-- **A pipeline handler is a handler of what is routed to `/raft`.** -/
theorem pipe_handlerFor (hServe : rafthttp.pipelineHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF) (hl : Loc)
    (pats : List GoString) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp -∗
      pipeHandlerOk Rh a γd Rs hl -∗
      http.handlerFor (raftHttpNet Rh) a Rs pats go!"/raft"
        (interface.mkOk (go.GoType.PointerType rafthttp.pipelineHandler.ty) #hl) := by
  iintro #Hpkg #Hh
  unfold http.handlerFor
  iexists _
  isplitr
  · ipureintro; rfl
  iintro !> %wi %r %R %γk %rd Hra %Hr #Hreq0 Htk Hbody Hw Hhd %Hfl HRs
  ihave #Hreq : (raftProto Rh).req R γk $$ []
  · rw [show (raftProto Rh).req R γk = ((raftHttpNet Rh).proto a).req R γk from rfl]
    iexact Hreq0
  iapply (hServe Rh a γd Rs hl wi r R γk rd Hr.1 (http.route_raft _ _ Hr.2)) $$ Hpkg Hh Hra Hreq Htk
    Hbody Hw Hhd %Hfl HRs

/-- **A stream handler is a handler of what is routed to the stream prefix.** -/
theorem stream_handlerFor (hServe : rafthttp.streamHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (Rh : RaftHttp GF) (a : GoString) (γd : GName) (Rs : IProp GF) (hl : Loc)
    (pats : List GoString) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp -∗
      streamHandlerOk Rh a γd Rs hl -∗
      http.handlerFor (raftHttpNet Rh) a Rs pats go!"/raft/stream/"
        (interface.mkOk (go.GoType.PointerType rafthttp.streamHandler.ty) #hl) := by
  iintro #Hpkg #Hh
  unfold http.handlerFor
  iexists _
  isplitr
  · ipureintro; rfl
  iintro !> %wi %r %R %γk %rd Hra %Hr #Hreq0 Htk Hbody Hw Hhd %Hfl HRs
  ihave #Hreq : (raftProto Rh).req R γk $$ []
  · rw [show (raftProto Rh).req R γk = ((raftHttpNet Rh).proto a).req R γk from rfl]
    iexact Hreq0
  iapply (hServe Rh a γd Rs hl wi r R γk rd Hr.1 (http.route_stream _ _ Hr.2)) $$ Hpkg Hh Hra Hreq
    Htk Hbody Hw Hhd %Hfl HRs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **`t.Handler()`** of a started transport of the member `lid` owning `a` (`trFixed`), with its
snapshotter and directory, and its `addRemoteFromRequest` and `AddRemote` returning (premises until
6d): a handler of `a` for the
raft protocol, lending each invocation an `R` and a reader's token of the transport's lock. -/
theorem rafthttp.Transport.Handler_core
    (hNPH : rafthttp.newPipelineHandler.spec (GF := GF) (hG := hG))
    (hNSH : rafthttp.newStreamHandler.spec (GF := GF) (hG := hG))
    (hNSnH : rafthttp.newSnapshotHandler.spec (GF := GF) (hG := hG))
    (hNewHandler : probing.NewHandler.spec (GF := GF) (hG := hG))
    (hGet : rafthttp.Transport.Get.spec (GF := GF) (hG := hG))
    (hPServe : rafthttp.pipelineHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (hSServe : rafthttp.streamHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs γr : GName)
    (a : GoString) (ss : Loc) (Rm : w64 → IProp GF) (Hown : Rh.owner a = lid) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trFixed Rh t lid γd R ∗
        t.[rafthttp.Transport, go!"Snapshotter"] ↦□ ss ∗ snap.isSnapshotter ss ∗
        inv snapDirN (snapDirInv ss γd Rh.γn.N.img Rm) ∗
        trAddRemoteReq t ∗ trAddRemote t }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Handler")) (Val #()))
    {{ (h : GoInterface), RET #h;
        http.handlerOk (raftHttpNet Rh) a iprop(R ∗ trReadTok Rh t lid γd R γs γr) h }} := by
  wp_start as ⟨#Htr, #Hssf, #Hss, #Hdir, #Harr, #HAddR⟩
  ihave #Htr' := Htr
  iunfold trFixed at Htr'
  icases Htr' with ⟨%lg, %ls, %ss0, %turls, %tuvs, %cid, %r, %ec, %srt, %prt, %drf, %ppr, %spr,
    #Hlg, %Hlgnn, #Hlid, #HtURLs, #Htuvs, #Hcid, #Hr, #Hraft, #Hec, #Hsrt, #Hsrtok, #Hprt, #Hprtok,
    #Hdrf, #Hls, %Hlsnn, #Hss0, %Hssnn, #Hppr, #Hspr, #Hreg, #Hpreg, #HPfx⟩
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, #HRP, #HPP, -, #HSP, -⟩
  ihave #HraftRs := netRaftOk_frame Rh.γn lid γd R (trReadTok Rh t lid γd R γs γr) r $$ Hraft
  wp_alloc_auto
  wp_auto
  wp_apply hNPH Rh a γd iprop(R ∗ trReadTok Rh t lid γd R γs γr) t r cid lg lid Hlgnn Hown $$ []
    as %hp ⟨%hpl, %Hhp, #Hhpok⟩
  · iunfold trAddRemoteReq at Harr
    iframe #
  (try wp_auto)
  wp_apply hNSH Rh a γd iprop(R ∗ trReadTok Rh t lid γd R γs γr) t
    ⟨go.GoType.PointerType rafthttp.Transport.ty, #t⟩ r lid cid lg Hlgnn Hown $$ []
    as %hs ⟨%hsl, %Hhs, #Hhsok⟩
  · iunfold trAddRemote at HAddR
    iframe #
    iintro !> %pid %Φ' !> ⟨HR, Htok⟩ HΦ'
    wp_apply hGet Rh t lid γd R γs γr pid $$ [$Htok] as %pi ⟨Htok, Hpi⟩
    iapply HΦ'
    iframe
    icases Hpi with (%Hn | ⟨%p, %Hp, #Hpok⟩)
    · ileft; ipureintro; exact Hn
    · iright; iexists p
      isplitr
      · ipureintro; exact Hp
      iapply peerStreams_of_peerOk $$ Hpok
  (try wp_auto)
  wp_apply hNSnH Rh a γd R t r ss cid lid Rm Hown $$ [] as %hsn #Hsnok
  · iunfold trAddRemoteReq at Harr
    iframe #
  (try wp_auto)
  have hNSM := http.NewServeMux_ok (GF := GF)
  have hHdl := http.Handle_ok (GF := GF)
  unfold http.NewServeMux_spec at hNSM
  unfold http.Handle_spec at hHdl
  wp_apply hNSM as %m Hm
  (try wp_auto)
  wp_apply hHdl $$ [$Hm] as Hm
  · ipureintro; simp
  (try wp_auto)
  wp_apply hHdl $$ [$Hm] as Hm
  · ipureintro; simp
  (try wp_auto)
  wp_apply hHdl $$ [$Hm] as Hm
  · ipureintro; simp [snapPath]
  (try wp_auto)
  ihave #Hpbi : isPkgInit (PROP := IProp GF) pkg_id.github_com.xiang90.probing $$ []
  · iPkgInit
  wp_apply hNewHandler as %hpr #Hprok
  (try wp_auto)
  wp_apply hHdl $$ [$Hm] as Hm
  · ipureintro; simp [snapPath, probingPath]
  (try wp_auto)
  subst Hhp Hhs
  iapply HΦ
  ihave Hmux := http.mux_handlerOk_ok (raftHttpNet Rh) m _ a
    iprop(R ∗ trReadTok Rh t lid γd R γs γr) $$ Hm
  iapply Hmux
  · -- each registered handler handles what is routed to it
    simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil]
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iapply pipe_handlerFor hPServe $$ Hpkg Hhpok
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iapply stream_handlerFor hSServe $$ Hpkg Hhsok
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iunfold snapPath at Hsnok
      iapply Hsnok
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iapply Hprok
      · iintro !> %R' %γk %w %Hr
        rw [show (raftHttpNet Rh).proto a = raftProto Rh from rfl]
        iapply raftProto_resp_probing Rh R' γk _ w (http.route_probing _ _ Hr.2) (by decide)
      · ipureintro
        intro R' _
        exact verHdrOk_nil
    iapply BigSepL.bigSepL_nil.2
    itrivial
  · -- the mux's own `404` and `301`
    iintro !> %R' %γk %w %_ -
    rw [show (raftHttpNet Rh).proto a = raftProto Rh from rfl]
    isplitr
    · iapply raftProto_resp_of <;> decide
    · iapply raftProto_resp_of <;> decide
  · ipureintro
    intro R' loc _
    exact ⟨verHdrOk_nil, verHdrOk_set _ _ _ (by decide) verHdrOk_nil⟩
  done

end proof

end EtcdGrove
end Perennial
