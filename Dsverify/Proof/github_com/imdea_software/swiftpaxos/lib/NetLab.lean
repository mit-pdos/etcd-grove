/-
The lab's `net` vocabulary the replica's and the master's transport specs name (dsverify-lab
`harness/lean/Harness/Proof/net/Base.lean`, `GooseLang/Ext/NetConn/Specs.lean`), restated over
`Net/`'s (`Net/Proof/net/Base.lean`, `GooseLang/Ext/Net/Proto.lean`):

* `net.ownListener l lid a` (persistent): the `*TCPListener` `l` is this node's listener `lid`, shared
  between threads at `a` (`lisAt` and `lisInv`, what `accept_shared_au` takes; the lab's persistent
  listener).
* `net.ownTCPConn c cid side` (persistent): the lab's connection end, `connAt` and `connIs`.
* `net.newConnResult op side Pout Pin cv err`: a new end with its tokens, or an error (an
  `*OpError`; the lab's also said `cv = nil`, which `Net/`'s specs do not).
* Lab-shaped specs proved from `Net/`'s (named `*.labProof`, as `Net/` owns `*.wp_proof`):
  `net.DialTimeout.labProof`, `net.TCPConn.Close.labProof`, `net.TCPConn.RemoteAddr.labProof`.
* `nodeIp ip`: the lab's node-IP fact (its harness gave each node an IP and wildcard `Listen`s took
  it). **Port change**: `Net/` has no node IP (any machine may listen at any valid address, D6,
  D20, D21; every node here is on loopback), so it is `True`; what the lab derived from it (the
  address a wildcard listener serves) is the wildcard-listen hypothesis's (notes/dsv-swiftpaxos.md,
  "Wildcard `Listen`").
-/
module

public import Net.Proof.net.Base
public import GooseLang.Ext.Net.Proto
public import Net.Proof.net.DialTimeout
public import Net.Proof.net.Conn__Close
public import Net.Proof.net.Conn__RemoteAddr
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- See the file header. -/
def net.ownListener (l : Loc) (lid : w64) (a : GoString) : IProp GF :=
  iprop(∃ x : GoInterface, net.lisAt l lid x ∗
    lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) lid a)

instance net.ownListener_persistent (l : Loc) (lid : w64) (a : GoString) :
    Persistent (net.ownListener (GF := GF) l lid a) := by
  unfold net.ownListener; infer_instance

/-- See the file header. -/
def nodeIp (_ip : GoString) : IProp GF := iprop(True)

instance nodeIp_persistent (ip : GoString) : Persistent (nodeIp (GF := GF) ip) := by
  unfold nodeIp; infer_instance

theorem nodeIp_intro (ip : GoString) : ⊢ nodeIp (GF := GF) ip := by
  unfold nodeIp; iintro; ipureintro; trivial

/-- See the file header. -/
def net.ownTCPConn (c : Loc) (cid : Nat) (side : Bool) : IProp GF :=
  iprop(∃ (a : GoString) (la ra : GoInterface), net.connAt c cid side a la ra ∗
    connIs (Gg := hG.goose_globalGS) cid)

instance net.ownTCPConn_persistent (c : Loc) (cid : Nat) (side : Bool) :
    Persistent (net.ownTCPConn (GF := GF) c cid side) := by
  unfold net.ownTCPConn; infer_instance

/-- See the file header. -/
def net.newConnResult (_op : GoString) (side : Bool) (Pout Pin : Proto GF) (cv err : GoInterface) :
    IProp GF :=
  iprop((∃ (c : Loc) (cid : Nat),
      ⌜cv = interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c ∧ err = interface.nil⌝ ∗
      net.ownTCPConn c cid side ∗ connEnd (Gg := hG.goose_globalGS) cid side Pout Pin [] [] ∗
      connFresh (Gg := hG.goose_globalGS) cid side) ∨
    (∃ i, ⌜err = interface.ok i⌝ ∗ ⌜net.netErr err⌝))

end defs

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- `net`'s `errTimeout` and `poll.ErrDeadlineExceeded`'s values, from `net`'s initialization. -/
theorem net.et_ed_init :
    isPkgInit (PROP := IProp GF) pkg_id.net ⊢
      ∃ et ed : GoInterface, globalAddr net.errTimeout ↦□ et ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  iintro #Hpkg
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  ihave #Hed := github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll $$ Hpoll
  icases Hed with ⟨%ed, #Hed⟩
  ihave #Hi : net.isInit $$ []
  · with_unfolding_all iapply isPkgInit_access (PROP := IProp GF) pkg_id.net $$ Hpkg
  icases Hi with ⟨-, -, %p, #Het⟩
  iexists _, ed
  iframe Het Hed

/-- The lab's `net.DialTimeout.spec` (`"tcp"`), from `Net/`'s and `dial_au`. -/
theorem net.DialTimeout.labProof (a : GoString) (d : w64) (P Q : Proto GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ addrProto (Gg := hG.goose_globalGS) a P Q }}
      (App (App (App (Val (@! net.DialTimeout)) (Val #(go!"tcp"))) (Val #a)) (Val #d))
    {{ (cv err : GoInterface), RET (PairV #cv #err);
        net.newConnResult go!"dial" false P Q cv err }} := by
  iintro %Φ ⟨#Hpkg, #Ha⟩ HΦ
  icases net.et_ed_init $$ Hpkg with ⟨%et, %ed, #Het, #Hed⟩
  ihave %Hok := addrTok_ok a $$ [Ha]
  · iapply addrProto_tok $$ Ha
  iapply net.DialTimeout.wp_proof go!"tcp" net.tcpNet_tcp a d et ed iprop(True)
    (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false P Q [] [] ∗
      connFresh (Gg := hG.goose_globalGS) cn false)) $$ []
  · iframe Het Hed
    isplitr
    · ipureintro; exact Hok
    isplit
    · itrivial
    · iapply dial_au a P Q $$ Ha
  iintro !> %cv %err Hres
  iapply HΦ
  unfold net.newConnResult
  icases Hres with (⟨%Herr, %cn, #Hc, Hend, Hfr⟩ | ⟨-, %x, %e, -, #Herr, -⟩)
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    ileft
    iexists t, cn
    isplitr
    · ipureintro; exact ⟨Hct, rfl⟩
    ihave #Hcs : connIs (Gg := hG.goose_globalGS) cn $$ [Hend]
    · iunfold connEnd at Hend
      icases Hend with ⟨Hs, -⟩
      iapply sendTok_connIs $$ Hs
    iframe Hend Hfr
    unfold net.ownTCPConn
    iexists a, la, ra
    iframe Hca Hcs
  · iright
    ihave %Hn := net.opErr_netErr _ _ _ _ _ $$ Herr
    obtain ⟨pe, rfl⟩ := Hn
    iexists _
    isplitr
    · ipureintro; rfl
    ipureintro; exact ⟨pe, rfl⟩

end specs

end Perennial
