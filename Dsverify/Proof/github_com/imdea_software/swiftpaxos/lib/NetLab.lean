/-
The lab's `net` vocabulary the replica's and the master's transport specs name (dsverify-lab
`harness/lean/Harness/Proof/net/Base.lean`, `GooseLang/Ext/NetConn/Specs.lean`), restated over
`Net/`'s (`Net/Proof/net/Base.lean`, `GooseLang/Ext/Net/Proto.lean`):

* `net.ownListener l lid la` (persistent): the `*TCPListener` `l` is this node's listener `lid` at
  `la` (a valid address or a wildcard, D21), shared between threads (`lisAt`, `netLisOn` and
  `lisInv`, what `accept_lis_shared_au` takes; the lab's persistent listener).
* `net.Listen.labProof`, `net.TCPListener.Accept.labProof`: the lab's `ListenWild`/`Accept` over
  `Net/`'s `Listen.spec`/`Listener.Accept.spec`, a listener's protocols given by `lisProto la P Q`
  (`listen_lis_au`, `accept_lis_shared_au`; the deployment's boot makes it, `lis_set_proto`).
* `net.ownTCPConn c cid side` (persistent): the lab's connection end, `connAt` and `connIs`.
* `net.newConnResult op side Pout Pin cv err`: a new end with its tokens, or an error (an
  `*OpError`; the lab's also said `cv = nil`, which `Net/`'s specs do not).
* Lab-shaped specs proved from `Net/`'s (named `*.labProof`, as `Net/` owns `*.wp_proof`):
  `net.DialTimeout.labProof`, `net.Dial.labProof`, `net.TCPConn.Close.labProof`, `net.TCPConn.RemoteAddr.labProof`.
* `nodeIp ip`: the lab's node-IP fact (its harness gave each node an IP and wildcard `Listen`s took
  it). **Port change**: `Net/` has no node IP (any machine may listen at any valid address, D6,
  D20, D21; every node here is on loopback), so it is `True`; what the lab derived from it (the
  address a wildcard listener serves) is the wildcard-listen hypothesis's (notes/dsv-swiftpaxos.md,
  "Wildcard `Listen`").
-/
module

public import Net.Proof.net.Base
public import GooseLang.Ext.Net.Proto
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.LibDeps

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
def net.ownListener (l : Loc) (lid : w64) (la : GoString) : IProp GF :=
  iprop(∃ x : GoInterface, net.lisAt l lid x ∗
    netLisOn (extLocalGS netExt (L := hG.goose_localGS)) lid la ∗
    lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) lid la)

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
theorem net.DialTimeout.labProof [github_com.imdea_software.swiftpaxos.SwiftNetDeps GF] (a : GoString) (d : w64) (P Q : Proto GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net ∗ addrProto (Gg := hG.goose_globalGS) a P Q }}
      (App (App (App (Val (@! net.DialTimeout)) (Val #(go!"tcp"))) (Val #a)) (Val #d))
    {{ (cv err : GoInterface), RET (PairV #cv #err);
        net.newConnResult go!"dial" false P Q cv err }} := by
  iintro %Φ ⟨#Hpkg, #Ha⟩ HΦ
  icases net.et_ed_init $$ Hpkg with ⟨%et, %ed, #Het, #Hed⟩
  ihave %Hok := addrTok_ok a $$ [Ha]
  · iapply addrProto_tok $$ Ha
  iapply (github_com.imdea_software.swiftpaxos.SwiftNetDeps.dialTimeout (GF := GF)) go!"tcp" net.tcpNet_tcp a d et ed iprop(True)
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

/-- The lab's `net.Dial.spec` (`"tcp"`), from `Net/`'s and `dial_au`. -/
theorem net.Dial.labProof [github_com.imdea_software.swiftpaxos.SwiftNetDeps GF] (a : GoString) (P Q : Proto GF) :
    {{ addrProto (Gg := hG.goose_globalGS) a P Q }}
      (App (App (Val (@! net.Dial)) (Val #(go!"tcp"))) (Val #a))
    {{ (cv err : GoInterface), RET (PairV #cv #err);
        net.newConnResult go!"dial" false P Q cv err }} := by
  iintro %Φ #Ha HΦ
  ihave %Hok := addrTok_ok a $$ [Ha]
  · iapply addrProto_tok $$ Ha
  iapply (github_com.imdea_software.swiftpaxos.SwiftNetDeps.dial (GF := GF)) go!"tcp" net.tcpNet_tcp a iprop(True)
    (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false P Q [] [] ∗
      connFresh (Gg := hG.goose_globalGS) cn false)) $$ []
  · isplitr
    · ipureintro; exact Hok
    isplit
    · itrivial
    · iapply dial_au a P Q $$ Ha
  iintro !> %cv %err Hres
  iapply HΦ
  unfold net.newConnResult
  icases Hres with (⟨%Herr, %cn, #Hc, Hend, Hfr⟩ | ⟨-, %x, -, #Herr⟩)
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
    ihave %Hn := net.resErr_netErr _ _ _ _ _ _ _ $$ Herr
    obtain ⟨pe, rfl⟩ := Hn.2 (by simp)
    iexists _
    isplitr
    · ipureintro; rfl
    ipureintro; exact ⟨pe, rfl⟩

/-- The lab's wildcard `Listen` (`net.ListenWild`), over `lisProto` (D21): `Listen("tcp", la)` at a
listener address `la` whose protocols are `P`, `Q`. -/
theorem net.Listen.labProof [github_com.imdea_software.swiftpaxos.SwiftNetDeps GF] (la : GoString) (P Q : Proto GF) :
    {{ lisProto (Gg := hG.goose_globalGS) la P Q }}
      (App (App (Val (@! net.Listen)) (Val #(go!"tcp"))) (Val #la))
    {{ (lv er : GoInterface), RET (PairV #lv #er);
        (∃ (ll : Loc) (lid : w64),
          ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #ll ∧
            er = interface.nil⌝ ∗ net.ownListener ll lid la) ∨
        (∃ i, ⌜er = interface.ok i⌝) }} := by
  iintro %Φ #Hlp HΦ
  ihave #Hlp' := Hlp
  iunfold lisProto at Hlp'
  icases Hlp' with ⟨-, -, %Hok⟩
  iapply wp_fupd
  iapply (github_com.imdea_software.swiftpaxos.SwiftNetDeps.listen (GF := GF)) go!"tcp" net.tcpNet_tcp la $$ []
  · isplitr
    · ipureintro; exact Hok
    iapply listen_lis_au la P Q $$ Hlp
  iintro !> %lv %er Hres
  icases Hres with (⟨%Her, %l, #Hli, Hnl, #Hon⟩ | ⟨%x, -, #Herr⟩)
  · subst Her
    imod lisInv_alloc ⊤ _ l la true $$ Hnl with #Hinv
    imodintro
    iapply HΦ
    ileft
    unfold net.isListener
    icases Hli with ⟨%t, %x, %Hlt, #Hat⟩
    iexists t, l
    isplitr
    · ipureintro; exact ⟨Hlt, rfl⟩
    unfold net.ownListener
    iexists x
    iframe Hat Hon Hinv
  · ihave %Hn := net.resErr_netErr _ _ _ _ _ _ _ $$ Herr
    obtain ⟨pe, rfl⟩ := Hn.2 (by simp)
    imodintro
    iapply HΦ
    iright
    iexists _
    ipureintro; rfl

/-- `Listen("tcp", la)` at a listener address `la` (`listenOk`), with the right to listen there as
`Net/`'s `Listen.spec` takes it (the update; models-rpc-http's `rpcLisP_lis` gives it). -/
theorem net.Listen.labProofU [github_com.imdea_software.swiftpaxos.SwiftNetDeps GF] (la : GoString) (hok : listenOk la = true) :
    {{ |={⊤,∅}=> lisToks (NG (Gg := hG.goose_globalGS)) la ∗
        (lisToks (NG (Gg := hG.goose_globalGS)) la ={∅,⊤}=∗ True) }}
      (App (App (Val (@! net.Listen)) (Val #(go!"tcp"))) (Val #la))
    {{ (lv er : GoInterface), RET (PairV #lv #er);
        (∃ (ll : Loc) (lid : w64),
          ⌜lv = interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #ll ∧
            er = interface.nil⌝ ∗ net.ownListener ll lid la) ∨
        (∃ i, ⌜er = interface.ok i⌝) }} := by
  iintro %Φ Hu HΦ
  iapply wp_fupd
  iapply (github_com.imdea_software.swiftpaxos.SwiftNetDeps.listen (GF := GF)) go!"tcp" net.tcpNet_tcp la $$ [Hu]
  · isplitr
    · ipureintro; exact hok
    iexact Hu
  iintro !> %lv %er Hres
  icases Hres with (⟨%Her, %l, #Hli, Hnl, #Hon⟩ | ⟨%x, -, #Herr⟩)
  · subst Her
    imod lisInv_alloc ⊤ _ l la true $$ Hnl with #Hinv
    imodintro
    iapply HΦ
    ileft
    unfold net.isListener
    icases Hli with ⟨%t, %x, %Hlt, #Hat⟩
    iexists t, l
    isplitr
    · ipureintro; exact ⟨Hlt, rfl⟩
    unfold net.ownListener
    iexists x
    iframe Hat Hon Hinv
  · ihave %Hn := net.resErr_netErr _ _ _ _ _ _ _ $$ Herr
    obtain ⟨pe, rfl⟩ := Hn.2 (by simp)
    imodintro
    iapply HΦ
    iright
    iexists _
    ipureintro; rfl

/-- The lab's `TCPListener.Accept` (shared listener), over `lisProto` (D21): a new end, the acceptor
writing `Q`, reading `P`. -/
theorem net.TCPListener.Accept.labProof [github_com.imdea_software.swiftpaxos.SwiftNetDeps GF] (ll : Loc) (lid : w64) (la : GoString) (P Q : Proto GF) :
    {{ net.ownListener ll lid la ∗ lisProto (Gg := hG.goose_globalGS) la P Q }}
      (App (Val #(methods (go.GoType.PointerType net.TCPListener.ty) go!"Accept" #ll)) (Val #()))
    {{ (cv err : GoInterface), RET (PairV #cv #err);
        net.newConnResult go!"accept" true Q P cv err }} := by
  iintro %Φ ⟨#Hl, #Hlp⟩ HΦ
  iunfold net.ownListener at Hl
  icases Hl with ⟨%x, #Hat, #Hon, #Hinv⟩
  iapply (github_com.imdea_software.swiftpaxos.SwiftNetDeps.accept (GF := GF)) ll lid x la (fun _ => iprop(True))
    (fun _ cn => iprop(connEnd (Gg := hG.goose_globalGS) cn true Q P [] [] ∗
      connFresh (Gg := hG.goose_globalGS) cn true)) $$ []
  · iframe Hat Hon
    iapply accept_lis_shared_au la P Q _ lid $$ Hlp Hinv
  iintro !> %cv %err Hres
  iapply HΦ
  unfold net.newConnResult
  icases Hres with (⟨%Herr, %cn, %a, -, #Hc, Hend, Hfr⟩ | ⟨%k, -, #Herr⟩)
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %la', %ra, %Hct, #Hca⟩
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
    iexists a, la', ra
    iframe Hca Hcs
  · iright
    ihave %Hn := net.resErr_netErr _ _ _ _ _ _ _ $$ Herr
    obtain ⟨pe, rfl⟩ := Hn.2 (by simp)
    iexists _
    isplitr
    · ipureintro; rfl
    ipureintro; exact ⟨pe, rfl⟩

end specs

end Perennial
