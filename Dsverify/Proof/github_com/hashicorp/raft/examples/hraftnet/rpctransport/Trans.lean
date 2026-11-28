/-
The vocabulary of the hraft kit transport's specs (`rpctransport.Transport`, its pipelines and its
receiver `RaftRPC`; notes/dsv-hraft.md, S4): server `i`'s transport `t` (`isTrans`, persistent)
holds its address `i`, its consumer channel (server `i`'s RPC channel, `isRpcChan`), its peers (each
raft address `a` a connection to a net/rpc server whose `RaftRPC` service is `raftSvc` of `a`), the
heartbeat handler under its mutex (`hbInv`: none, or one with `hbHandler`), and the registered codec
with its sender laws (`CodecLaws`, taken as a hypothesis: `CodecLaws.lean`). The errors the
transport makes are `errors.New` errors (`errStr`: an `*errorString`, so `errOk` and `errNoFmt`).
A pipeline (`isPip`) is examples/inproc's (the lab's `PipeBase.lean`), over `isTrans`; the
receiver (`isRcv`) is a `*RaftRPC` of a transport.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Facts
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.CodecLaws
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn
public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet.rpctransport

open github_com.hashicorp.raft github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

/-- The net/rpc service name of the receiver (`Receiver`, registered as `"RaftRPC"`). -/
abbrev svcName : GoString := go!"RaftRPC"

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : Net.NetProtoGS]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-! ## The transport -/

/-- The transport's mutex holds the heartbeat handler: none (`nil`), or one with the contract
`hbHandler γ i`. -/
def hbInv (γ : GNames) (i : SID) (t : Loc) : IProp GF :=
  iprop(∃ f : GoFunc, t.[Transport, go!"hb"] ↦ f ∗ (⌜f = func.nil⌝ ∨ hbHandler γ i f))

/-- The net/rpc address `na` of the rpc world `W` serves raft address `a`'s receiver: its `RaftRPC`
service's spec `S` accepts every deposit of `raftSvc γ snapP a` (persistent). `S` is `raftSvc γ snapP a`
itself, or a wider spec the world fixed before `γ` was known (the hraft kit's: the protocol of the
first configuration the orchestrator draws, S5d). -/
def svcAt (γ : GNames) (snapP : Nat → List w8 → IProp GF) (W : net.rpc.RpcWorld GF) (a na : GoString) :
    IProp GF :=
  iprop(∃ S : net.rpc.MethodSpec GF, ⌜W.SS na svcName = some S⌝ ∗
    □ (∀ (M : GoString) (bs : List w8) (Φ : List w8 → GoString → IProp GF),
        raftSvc γ snapP a M bs Φ -∗ S M bs Φ))

instance svcAt_persistent γ snapP W a na : Persistent (svcAt (GF := GF) γ snapP W a na) := by
  unfold svcAt; infer_instance

/-- `svcAt` of a world whose spec is `raftSvc γ snapP a` itself. -/
theorem svcAt_of_eq (γ : GNames) (snapP : Nat → List w8 → IProp GF) (W : net.rpc.RpcWorld GF)
    (a na : GoString) (h : W.SS na svcName = some (raftSvc γ snapP a)) :
    ⊢ svcAt (GF := GF) γ snapP W a na := by
  unfold svcAt
  iexists raftSvc γ snapP a
  isplitr; · ipureintro; exact h
  imodintro
  iintro %M %bs %Φ H
  iexact H

/-- The peer of raft address `a` is the connection `p` to a net/rpc server of the rpc world `W`
that serves `a`'s receiver (`svcAt`). -/
def peerOk (γ : GNames) (snapP : Nat → List w8 → IProp GF) (W : net.rpc.RpcWorld GF) (a : GoString)
    (p : Loc) : IProp GF :=
  iprop(∃ na : GoString, isConn p W na ∗ svcAt γ snapP W a na)

instance peerOk_persistent γ snapP W a p : Persistent (peerOk (GF := GF) γ snapP W a p) := by
  unfold peerOk; infer_instance

/-- **Server `i`'s transport `t`** in protocol `γ` (persistent): its fields (never written after
`New` but `hb`), its consumer channel (`i`'s RPC channel), its peers (`peerOk`), the heartbeat
handler under its mutex (`hbInv`), and the registered codec `C` with the sender's laws. -/
def isTrans (t : Loc) (γ : GNames) (snapP : Nat → List w8 → IProp GF) (i : SID)
    (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) : IProp GF :=
  iprop(∃ (d : w64) (ch pm : Loc) (P : GMap GoString Loc),
    "#Hlocal" ∷ t.[Transport, go!"local"] ↦□ (i : GoString) ∗
    "#Htimeout" ∷ t.[Transport, go!"timeout"] ↦□ d ∗
    "#Hconsumer" ∷ t.[Transport, go!"consumer"] ↦□ ch ∗
    "#Hrpc" ∷ isRpcChan γ snapP i ch ∗
    "#Hpeers" ∷ t.[Transport, go!"peers"] ↦□ pm ∗
    "#Hpm" ∷ pm ↦$□ P ∗
    "#HP" ∷ ([∗map] a ↦ p ∈ P, peerOk γ snapP W a p) ∗
    "#Hmu" ∷ sync.isMutex (t.[Transport, go!"mu"]) (hbInv γ i t) ∗
    "#Hcodec" ∷ net.rpc.codecSet C ∗
    "%Hlaws" ∷ ⌜CodecLaws C⌝)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1000 in
instance isTrans_persistent t γ snapP i W C : Persistent (isTrans (GF := GF) t γ snapP i W C) := by
  unfold isTrans; infer_instance

/-- **The receiver** `s` (a `*RaftRPC`) of server `i`'s transport. -/
def isRcv (s : Loc) (γ : GNames) (snapP : Nat → List w8 → IProp GF) (i : SID)
    (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) : IProp GF :=
  iprop(∃ t : Loc, s ↦□ RaftRPC.mk t ∗ isTrans t γ snapP i W C)

instance isRcv_persistent s γ snapP i W C : Persistent (isRcv (GF := GF) s γ snapP i W C) := by
  unfold isRcv; infer_instance

/-! ## The transport's errors -/

/-- An `errors.New` error (an `*errors.errorString`) whose `Error()` returns some message. -/
def errStr (err : GoInterface) : IProp GF :=
  iprop(∃ (x : Loc) (msg : GoString),
    ⌜err = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x⌝ ∗
    □ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x)) (Val #()))
        {{ Φ }})

instance errStr_persistent err : Persistent (errStr (GF := GF) err) := by
  unfold errStr; infer_instance

/-- `errors.New`'s result (`errors.wp_New_errorString`'s post) is an `errStr`. -/
theorem errStr_intro (x : Loc) (msg : GoString) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x)) (Val #()))
        {{ Φ }}) ⊢ errStr (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) := by
  iintro #H
  unfold errStr
  iexists x, msg
  iframe H
  ipureintro; rfl

theorem errStr_errOk (err : GoInterface) : errStr (GF := GF) err ⊢ errOk err := by
  unfold errStr errOk
  iintro ⟨%x, %msg, %he, #HE⟩
  subst he
  iexists ⟨go.GoType.PointerType errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %Φ HΦ
  iapply HE
  inext
  iapply HΦ

/-- `errors.New`'s errors (`*errors.errorString`, method set `{Error() string}`) implement `error`
and have no `Format` method (the lab's `errorString_errNoFmt`). -/
theorem errorString_errNoFmt (x : Loc) :
    errNoFmt (GF := GF) (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) := by
  refine ⟨_, rfl, ?_, ?_⟩
  · have h := go.MethodSetIs.method_set_is (t := go.GoType.PointerType errors.errorString.ty) go!"Format"
    simpa [go.methodSetLookup] using h
  · have h := go.MethodSetIs.method_set_is (t := go.GoType.PointerType errors.errorString.ty) go!"Error"
    simpa [go.methodSetLookup] using h

theorem errStr_errNoFmt (err : GoInterface) : errStr (GF := GF) err ⊢ ⌜errNoFmt (GF := GF) err⌝ := by
  unfold errStr
  iintro ⟨%x, %msg, %he, -⟩
  subst he
  ipureintro; exact errorString_errNoFmt x

/-- A raft error variable (`errors.New`'s, `errVals`) holds an error with a callable `Error()`. -/
theorem newVar_errOk (X msg : GoString) :
    errors.newVar (GF := GF) X msg ⊢
      ∃ e : GoInterface, globalAddr X ↦□ e ∗ errOk e := by
  unfold errors.newVar errOk
  iintro ⟨%x, #Hx, -, #HE⟩
  iexists _
  iframe Hx
  iexists ⟨go.GoType.PointerType errors.errorString.ty, #x⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %Φ HΦ
  iapply HE
  inext
  iapply HΦ

/-- raft's `ErrPipelineShutdown` holds an error with a callable `Error()`. -/
theorem pipeShutdown_ok :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ⊢
      ∃ e : GoInterface, globalAddr ErrPipelineShutdown ↦□ e ∗ errOk e := by
  iintro #H
  ihave #Hn := newVar_of_init RaftErr.pipelineShutdown $$ H
  have hv : RaftErr.pipelineShutdown.var = ErrPipelineShutdown := rfl
  rw [← hv]
  iapply newVar_errOk $$ Hn

/-! ## Answers -/

/-- The continuation a sender deposits with a request whose success answers are `ok`: any error
message, or a success answer. -/
def okAns (ok : List w8 → IProp GF) (rep : List w8) (msg : GoString) : IProp GF :=
  iprop(⌜msg ≠ []⌝ ∨ ok rep)

theorem answers_okAns (ok : List w8 → IProp GF) : ⊢ answers (GF := GF) ok (okAns ok) := by
  unfold answers okAns
  isplitl
  · iintro %rep Hok; iright; iexact Hok
  · iintro %msg %Hm; ileft; ipureintro; exact Hm

/-! ## Pipelines (examples/inproc's, the lab's `PipeBase.lean`) -/

/-- What closing a future's `done` channel broadcasts: its `err` field is read-only, nil or an
error. -/
def futErrDone (f : Loc) : IProp GF :=
  iprop(∃ e : GoInterface, f.[appendFuture, go!"err"] ↦□ e ∗ (⌜e = interface.nil⌝ ∨ errOk e))

instance futErrDone_persistent f : Persistent (futErrDone (GF := GF) f) := by
  unfold futErrDone; infer_instance

/-- A future whose `Error()` can be called (persistent): its `done` channel broadcasts
`futErrDone`. -/
def futDone (f : Loc) : IProp GF :=
  iprop(∃ (dc : Loc) (γd : ChanNames), f.[appendFuture, go!"done"] ↦□ dc ∗
    ownBroadcastChan dc γd (futErrDone f) .Unknown)

instance futDone_persistent f : Persistent (futDone (GF := GF) f) := by
  unfold futDone; infer_instance

/-- **A queued future** `f` of a pipeline of term `T`: its read-only fields, the right to write its
`err` and to close its `done`, the request (read-only, valid, of term `T`) and the lent response
struct (`Success = false`). -/
def futQ (γ : GNames) (T : Nat) (f : Loc) : IProp GF :=
  iprop(∃ (ts : time.Time) (args resp dc : Loc) (γd : ChanNames) (rq : AppendEntriesRequest)
      (rp0 : AppendEntriesResponse) (snd : SID) (prev pt : Nat) (ents : RLog) (lci : Nat) (ss : Snap),
    "#Hstart" ∷ f.[appendFuture, go!"start"] ↦□ ts ∗
    "#Hreq" ∷ f.[appendFuture, go!"req"] ↦□ args ∗
    "#Hresp" ∷ f.[appendFuture, go!"resp"] ↦□ resp ∗
    "#Hdone" ∷ f.[appendFuture, go!"done"] ↦□ dc ∗
    "Herr" ∷ f.[appendFuture, go!"err"] ↦ interface.nil ∗
    "Hdc" ∷ ownBroadcastChan dc γd (futErrDone f) .Pending ∗
    "#Hargs" ∷ args ↦□ rq ∗
    "#Hrq" ∷ aeReq γ rq snd T prev pt ents lci ss ∗
    "Hrp" ∷ resp ↦ rp0 ∗
    "%Hrp0" ∷ ⌜rp0.Success' = false⌝)

/-- The pipeline's lock invariant: while `closed` is false, the right to close `closeCh`. -/
def pipLocked (p cc : Loc) (γcl : ChanNames) : IProp GF :=
  iprop(∃ b : Bool, p.[pipeline, go!"closed"] ↦ b ∗
    (⌜b = true⌝ ∨ ownBroadcastChan cc γcl iprop(True) .Pending))

/-- **The pipeline `p` to `j`, of term `T`** (persistent), on a transport `t`: its fields, the
queue (a bag of `futQ`), the consumer channel (a bag of `pipeFut`), its mutex and the close
channel. -/
def isPip (p : Loc) (γ : GNames) (j : SID) (T : Nat) : IProp GF :=
  iprop(∃ (t : Loc) (snapP : Nat → List w8 → IProp GF) (i : SID) (W : net.rpc.RpcWorld GF)
      (C : net.rpc.CodecSpec GF) (q cons cc : Loc) (γq γc γcl : ChanNames),
    "#Ht" ∷ p.[pipeline, go!"t"] ↦□ t ∗
    "#Hj" ∷ p.[pipeline, go!"target"] ↦□ (j : GoString) ∗
    "#Hq" ∷ p.[pipeline, go!"queue"] ↦□ q ∗
    "#Hc" ∷ p.[pipeline, go!"consumer"] ↦□ cons ∗
    "#Hcc" ∷ p.[pipeline, go!"closeCh"] ↦□ cc ∗
    "#Htr" ∷ isTrans t γ snapP i W C ∗
    "#Hqb" ∷ isChanBag (V := Loc) γq q (futQ γ T) ∗
    "#Hcb" ∷ isChanBag (V := GoInterface) γc cons (pipeFut γ j T) ∗
    "#Hlock" ∷ sync.isMutex (p.[pipeline, go!"mu"]) (pipLocked p cc γcl) ∗
    "#Hclose" ∷ ownBroadcastChan cc γcl iprop(True) .Unknown)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1000 in
instance isPip_persistent p γ j T : Persistent (isPip (GF := GF) p γ j T) := by
  unfold isPip; infer_instance

end defs

end github_com.hashicorp.raft.examples.hraftnet.rpctransport

end Perennial
