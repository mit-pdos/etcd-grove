/-
**The transport's state, from `Start`** (rafthttp stage 6d). Lean-first.
* `TrN`: the transport's names: its member, the receiver's snapshot directory, the resource its
  `Raft`'s calls borrow, and its lock's two ghost records.
* `netHttpOk` (persistent): the network's streams' registry and every member's hosts registered
  with the raft protocol (the program's start, D34a), what a transport's peers post to.
* `trState` (persistent): a started transport: its fixed fields (`trFixed`), probers, stop rights'
  invariant, the guard of its lock, the snapshotter's directory; `trLive` with the half of `γr`
  that `AddPeer`/`AddRemote` update; `trFrozen` after the freeze (`trRemotesFrozen`); `trTok`, a
  reader's token of its lock.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportInv
public import Proof.net.http.Axioms

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

/-- **The transport's names** (stage 6d): its member `lid`, the receiver's snapshot directory
`γd`, the resource `R` its `Raft`'s calls borrow, its lock's ghost records `γs` (the maps) and
`γr` (the ids added, the stopped flag). -/
structure TrN (GF : BundledGFunctors) where
  lid : w64
  γd : GName
  R : IProp GF
  γs : GName
  γr : GName

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The network's HTTP side, ready for the member `lid`** (persistent): the streams' registry,
and every other member's hosts registered with the raft protocol (`pipeReg`: the program's start
reserves them, D34a), what the member's peers post to. -/
def netHttpOk (γn : NetNames GF) (lid : w64) : IProp GF :=
  iprop(streamRegInv (netRh γn) ∗
    □ ∀ pid : w64, ⌜(netRh γn).member pid ∧ pid ≠ lid⌝ -∗ pipeReg (netRh γn) pid)

instance netHttpOk_persistent (γn : NetNames GF) (lid : w64) : Persistent (netHttpOk γn lid) := by
  unfold netHttpOk; infer_instance

/-- A host a member owns is one of its peer URLs' (`netOwner_mem`, through `netRh`). -/
theorem netRh_owner_mem (γn : NetNames GF) (h : GoString) (pid : w64) (hd0 : γn.dir 0 = [])
    (ho : (netRh γn).owner h = pid) (hm : (netRh γn).member pid) :
    go!"http://" ++ h ∈ γn.dir pid := by
  rw [netRh_owner] at ho
  exact netOwner_mem γn.dir h pid hd0 ho ((netRh_member γn pid).1 hm)

/-- **The network's HTTP side from its directory** (stage 6d): the streams' registry and every host
of another member's peer URL registered with the raft protocol (the program's start reserves
each, `http.reserve`), with no member `0` (the owner the directory gives an unknown host). -/
theorem netHttpOk_of_dir (γn : NetNames GF) (lid : w64) (hd0 : γn.dir 0 = []) :
    inv streamRegN iprop(∃ m : GMap GName StreamKey, ghostMapAuth γn.reg 1 m) ∗
      □ (∀ (id : w64) (h : GoString), ⌜id ≠ lid ∧ go!"http://" ++ h ∈ γn.dir id⌝ -∗
        http.httpProtoAt h (raftProto (netRh γn))) ⊢ netHttpOk γn lid := by
  iintro ⟨#Hreg, #Hdir⟩
  iunfold netHttpOk
  isplitr
  · iapply streamRegInv_netRh γn $$ Hreg
  imodintro
  iintro %pid %Hm
  iunfold pipeReg
  imodintro
  iintro %h %Ho
  have hh : go!"http://" ++ h ∈ γn.dir pid := netRh_owner_mem γn h pid hd0 Ho Hm.1
  have hp : pid ≠ lid ∧ go!"http://" ++ h ∈ γn.dir pid := ⟨Hm.2, hh⟩
  iapply Hdir $$ %pid %h %hp

/-- **A three-address network's HTTP side, reserved** (stage 6d; the examples' clusters): with every
host of the directory one of `a₁`, `a₂`, `a₃` and no member `0`, the program start's rights to fix
the three addresses' protocols reserve each for the raft protocol: the network's HTTP side for
every member (`netHttpOk`), and the right to serve each address with it (`httpProtoOwn`, for its
member's listener, `http.register`). -/
theorem netHttp_reserve3 (γn : NetNames GF) (a₁ a₂ a₃ : GoString) (hd0 : γn.dir 0 = [])
    (hhost : ∀ (i : w64) (h : GoString), go!"http://" ++ h ∈ γn.dir i → h = a₁ ∨ h = a₂ ∨ h = a₃) :
    ⊢ inv streamRegN iprop(∃ m : GMap GName StreamKey, ghostMapAuth γn.reg 1 m) -∗
      httpProtoFree a₁ -∗ httpProtoFree a₂ -∗ httpProtoFree a₃ ==∗
      (□ ∀ lid : w64, netHttpOk γn lid) ∗ http.httpProtoOwn a₁ (raftProto (netRh γn)) ∗
        http.httpProtoOwn a₂ (raftProto (netRh γn)) ∗ http.httpProtoOwn a₃ (raftProto (netRh γn)) := by
  iintro #Hreg Hf₁ Hf₂ Hf₃
  imod (http.reserve a₁ (raftProto (netRh γn))) $$ Hf₁ with ⟨#Hat₁, Ho₁⟩
  imod (http.reserve a₂ (raftProto (netRh γn))) $$ Hf₂ with ⟨#Hat₂, Ho₂⟩
  imod (http.reserve a₃ (raftProto (netRh γn))) $$ Hf₃ with ⟨#Hat₃, Ho₃⟩
  imodintro
  iframe Ho₁ Ho₂ Ho₃
  iintro !> %lid
  iapply netHttpOk_of_dir γn lid hd0 $$ [Hreg]
  iframe Hreg
  iintro !> %i %h %Hm
  rcases hhost i h Hm.2 with rfl | rfl | rfl
  · iexact Hat₁
  · iexact Hat₂
  · iexact Hat₃

/-- **The network's HTTP side of a one-member network** (stage 6d): no other member, so nothing to
register but the streams' registry. -/
theorem netHttpOk_single (γn : NetNames GF) (lid : w64)
    (hone : ∀ f, γn.dir f ≠ [] → f = lid) :
    inv streamRegN iprop(∃ m : GMap GName StreamKey, ghostMapAuth γn.reg 1 m) ⊢
      netHttpOk γn lid := by
  iintro #Hreg
  iunfold netHttpOk
  isplitr
  · iapply streamRegInv_netRh γn $$ Hreg
  imodintro
  iintro %pid %Hm
  exact absurd (hone pid Hm.1) Hm.2

/-- **A started transport `t` of the network `γn`, with the names `c`** (persistent). -/
def trState (γn : NetNames GF) (t : Loc) (c : TrN GF) : IProp GF :=
  iprop(trFixed (netRh γn) t c.lid c.γd c.R ∗ trProbers t ∗ trStopInv (netRh γn) c.R c.γs ∗
    sync.isRWMutexGuard (t.[rafthttp.Transport, go!"mu"])
      (trLockP (netRh γn) t c.lid c.γd c.R c.γs c.γr) ∗
    ∃ (ss : Loc) (Rm : w64 → IProp GF), t.[rafthttp.Transport, go!"Snapshotter"] ↦□ ss ∗
      snap.isSnapshotter ss ∗ inv snapDirN (snapDirInv ss c.γd γn.N.img Rm))

instance trState_persistent (γn : NetNames GF) (t : Loc) (c : TrN GF) :
    Persistent (trState γn t c) := by
  unfold trState; infer_instance

/-- **A live transport** (exclusive): started, not stopped, the ids `AddRemote` and `AddPeer`
were called for `rs` (`trIds`); `AddPeer`/`AddRemote` update it. -/
def trLive (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) : IProp GF :=
  iprop(trState γn t c ∗ ghostVar c.γr (1 : Qp).half (rs, false))

/-- **A frozen transport** (persistent): started, no more `AddPeer`/`AddRemote` from its owner,
the ids `rs` for good. -/
def trFrozen (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) : IProp GF :=
  iprop(trState γn t c ∗ trRemotesFrozen c.γr rs)

instance trFrozen_persistent (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) :
    Persistent (trFrozen γn t c rs) := by
  unfold trFrozen; infer_instance

/-- **A reader's token of the transport's lock** (exclusive): what `Send`, `Get`, `CutPeer` and
`MendPeer` take. -/
def trTok (γn : NetNames GF) (t : Loc) (c : TrN GF) : IProp GF :=
  trReadTok (netRh γn) t c.lid c.γd c.R c.γs c.γr

/-- **The freeze**: a live transport given up for good. -/
theorem trLive_freeze (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (E : CoPset) :
    ⊢ trLive γn t c rs ={E}=∗ trFrozen γn t c rs := by
  iintro Hl
  iunfold trLive at Hl
  icases Hl with ⟨#Hst, Hg⟩
  imod inv_alloc trRemN E iprop(∃ sb : Bool, ghostVar (GF := GF) c.γr (1 : Qp).half (rs, sb))
    $$ [Hg] with #Hi
  · inext; iexists false; iexact Hg
  imodintro
  iunfold trFrozen
  iframe Hst
  iunfold trRemotesFrozen
  iexact Hi

/-- The lock's reader tokens are the transport's (`n` kept abstract: the kernel would unfold a
literal count). -/
theorem trToks_mk (γn : NetNames GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF)
    (γs γr : GName) (n : Nat) :
    ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (t.[rafthttp.Transport, go!"mu"])
      (trLockP (netRh γn) t lid γd R γs γr)) ⊢
      [∗list] _x ∈ List.replicate n (), trTok γn t ⟨lid, γd, R, γs, γr⟩ := by
  unfold trTok trReadTok
  exact .rfl

end defs

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
/-- **`t.Start()`** on a transport the caller owns whole (`NewServer`'s literal, its mutex fresh),
its logger and stats set, of a member `tv.ID` of the network `γn` (with peer URLs), its URLs'
slice read-only, its `Raft` the member's (`netRaftOk`, borrowing `R`), its snapshotter and
directory, the network's HTTP side ready: an error, or the transport live with no peer or remote
yet, and all its lock's reader tokens. -/
theorem rafthttp.Transport.Start_full
    (hNSRT : rafthttp.newStreamRoundTripper.spec (GF := GF) (hG := hG))
    (hNRT : rafthttp.NewRoundTripper.spec (GF := GF) (hG := hG))
    (hNewProber : probing.NewProber.spec (GF := GF) (hG := hG))
    (hEvery : rate.Every.spec (GF := GF) (hG := hG))
    (γn : NetNames GF) (t : Loc) (tv : rafthttp.Transport) (R : IProp GF) (γd : GName)
    (Rm : w64 → IProp GF) (uvs : List net.url.URL) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        t ↦ tv ∗
        ⌜tv.Logger' ≠ null ∧ tv.ServerStats' ≠ null ∧ tv.LeaderStats' ≠ null ∧
          tv.mu' = zero_val _root_.Perennial.sync.RWMutex ∧ γn.dir tv.ID' ≠ []⌝ ∗
        tv.URLs' ↦*□ uvs ∗ □ netRaftOk γn tv.ID' γd R tv.Raft' ∗
        snap.isSnapshotter tv.Snapshotter' ∗
        inv snapDirN (snapDirInv tv.Snapshotter' γd γn.N.img Rm) ∗ netHttpOk γn tv.ID' }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"Start")) (Val #()))
    {{ (err : GoInterface), RET #err;
        ⌜err ≠ GoInterface.nil⌝ ∨
        ⌜err = GoInterface.nil⌝ ∗ ∃ c : TrN GF, ⌜c.lid = tv.ID' ∧ c.γd = γd ∧ c.R = R⌝ ∗
          trLive γn t c ([], []) ∗
          [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (), trTok γn t c }} := by
  wp_start_folded as ⟨Ht, %Hpre, #Huvs, #Hraft, #Hss, #Hdir, #Hnet⟩
  iStructNamed Ht
  obtain ⟨Hlgnn, Hssnn, Hlsnn, Hmu0, Hmem⟩ := Hpre
  iapply wp_fupd
  wp_apply (rafthttp.Transport.Start_core hNSRT hNRT hNewProber hEvery (raftHttpNet (netRh γn)) t
      tv.TLSInfo' tv.DialTimeout' (DFrac.own 1) (DFrac.own 1) tv.streamRt' tv.pipelineRt'
      tv.pipelineProber' tv.streamProber' tv.peers' tv.remotes' tv.DialRetryFrequency')
    $$ [TLSInfo DialTimeout streamRt pipelineRt peers remotes pipelineProber streamProber
      DialRetryFrequency]
    as %err ⟨TLSInfo, DialTimeout, Hres⟩
  · iframe
  icases Hres with (⟨%Hne, -⟩ | ⟨%Heq, %srt, %prt, %pp, %sp, %pm, %rm, %drf, Hsrt, #Hsrtok, Hprt,
    #Hprtok, Hpm, Hpmm, Hrm, Hrmm, Hpp, #Hppok, Hsp, #Hspok, Hdrf⟩)
  · imodintro
    iapply HΦ
    ileft; ipureintro; exact Hne
  subst Heq
  ihave %Hpmnn := ownMap_not_nil pm _ _ $$ Hpmm
  ihave %Hrmnn := ownMap_not_nil rm _ _ $$ Hrmm
  -- the ghost records and the stop rights' invariant
  imod ghostVar_alloc ((pm, rm, (∅ : GMap w64 GoInterface), (∅ : GMap w64 Loc)) : trRec)
    with ⟨%γs, Hgs⟩
  icases (ghostVar_split_half γs 1 _).1 $$ Hgs with ⟨Hgs1, Hgs2⟩
  imod ghostVar_alloc ((([], []) : trIds), false) with ⟨%γr, Hgr⟩
  icases (ghostVar_split_half γr 1 _).1 $$ Hgr with ⟨Hgr1, Hgr2⟩
  imod (inv_alloc trStopN ⊤ iprop(∃ (pm' rm' : Loc) (PM : GMap w64 GoInterface)
      (RM : GMap w64 Loc), ghostVar γs (1 : Qp).half ((pm', rm', PM, RM) : trRec) ∗
      ([∗map] id ↦ pi ∈ PM, ∃ p : Loc,
        ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
          peerStop (netRh γn) id R p) ∗
      ([∗map] id ↦ g ∈ RM, remoteStop (netRh γn) id R g))) $$ [Hgs2] with #Hstop
  · inext
    iexists pm, rm, ∅, ∅
    iframe Hgs2
    isplitl
    · iapply BigSepM.bigSepM_empty.2; itrivial
    · iapply BigSepM.bigSepM_empty.2; itrivial
  -- the lock
  rw [Hmu0]
  imod sync.init_RWMutex (trLockP (netRh γn) t tv.ID' γd R γs γr) (E := ⊤)
    (t.[rafthttp.Transport, go!"mu"]) $$ [Hpm Hrm Hpmm Hrmm Hgs1 Hgr1] mu with Htoks
  · inext
    iunfold trLockP
    iexists pm, rm, ∅, ∅, ([], []), false
    iframe Hpm Hrm Hgs1 Hgr1
    isplitl [Hpmm]
    · iunfold mapOrNil; iright; iexact Hpmm
    isplitl [Hrmm]
    · iunfold mapOrNil; iright; iexact Hrmm
    isplitr
    · ipureintro
      refine ⟨fun id h => by simp at h, fun _ => ⟨Hpmnn, Hrmnn⟩, fun _ id h => by simp at h⟩
    isplitr
    · imodintro; iunfold peersOk; iapply BigSepM.bigSepM_empty.2; itrivial
    · imodintro; iunfold remotesOk; iapply BigSepM.bigSepM_empty.2; itrivial
  ihave ⟨Htoks, #Hgd⟩ := sync.ownRWMutex_slots_guard _ _ $$ Htoks
  -- the fixed fields
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, #HSP, -⟩
  ipersist Logger; ipersist ID; ipersist URLs; ipersist ClusterID; ipersist Raft
  ipersist ErrorC; ipersist Hsrt; ipersist Hprt; ipersist Hdrf; ipersist LeaderStats
  ipersist ServerStats; ipersist Hpp; ipersist Hsp; ipersist Snapshotter
  iunfold netHttpOk at Hnet
  icases Hnet with ⟨#Hreg, #Hpreg⟩
  imodintro
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iexists ⟨tv.ID', γd, R, γs, γr⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  isplitl [Hgr2]
  · iunfold trLive
    iframe Hgr2
    iunfold trState
    simp only
    isplitr
    · iunfold trFixed
      iexists tv.Logger', tv.LeaderStats', tv.ServerStats', tv.URLs', uvs, tv.ClusterID', tv.Raft',
        tv.ErrorC', srt, prt, drf, pp, sp
      simp only [netRh]
      iframe #
      ipureintro; exact ⟨Hlgnn, Hlsnn, Hssnn, Hmem⟩
    isplitr
    · iunfold trProbers
      iexists pp, sp
      iframe #
    isplitr
    · iunfold trStopInv; iexact Hstop
    iframe #
  iapply trToks_mk $$ Htoks

end proof

end EtcdGrove
end Perennial
