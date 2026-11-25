/-
`clientListener`: a client connection's one `PROPOSE` (whose first bytes `serveConn` already
read), its writer registered under `r.M` with the reply token, its `proposal` sent on
`ProposeChan`; the protocol allows no more bytes, so the next read fails and the connection is
closed.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.LibDeps
public import Net.Proof.net.ConnIo
public import Net.Proof.net.Errors
public import Proof.bufio.Own
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.PrefixReader
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.DelayChan
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.ClientWire
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Log
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Stream
public import Perennial.Proof.strings.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

/-- The lab's `net.TCPConn.RemoteAddr.wp_String` (proved below, `tcpAddrString`): `String()` of a `*TCPAddr` returns some string.
`clientListener` uses only that it returns (`strings.Split(conn.RemoteAddr().String(), ":")[0]`,
for `IsProxy` on an empty `ProxyInfo` and `WaitDuration` on a nil latency table). -/
def TCPAddrStringHyp : Prop :=
  ∀ (pa : Loc) (v : net.TCPAddr),
  {{ (pa ↦□ v : IProp GF) }}
    (App (Val #(methods (go.GoType.PointerType net.TCPAddr.ty) go!"String" #pa)) (Val #()))
  {{ (s : GoString), RET #s; True }}

/-- `TCPAddrStringHyp` holds of `Net/`'s model (`models/net/model.go`'s `TCPAddr.String`, `extAnyString`: an
arbitrary string): dsv-swiftpaxos's `net.wp_TCPAddr_String` (`lib/NetConn.lean`). -/
theorem tcpAddrString : TCPAddrStringHyp (GF := GF) := by
  intro pa v
  wp_start
  wp_auto
  wp_apply net.wp_extAnyString as %s
  iapply HΦ
  itrivial

variable [EpBufioDeps GF] [EpNetDeps GF]

/-- `Close()` of a connection whose outcome nobody keeps (`net.Conn.Close.spec` by `close_au`). -/
theorem wp_connClose (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    {{ net.connAt (GF := GF) t cn s a la ra ∗ connIs (Gg := hG.goose_globalGS) cn }}
      (App (Val #(methods (go.GoType.PointerType net.TCPConn.ty) go!"Close" #t)) (Val #()))
    {{ (err : GoInterface), RET #err; True }} := by
  iintro %Φ ⟨#Hc, #Hi⟩ HΦ
  iapply (EpNetDeps.connClose t cn s a la ra (fun _ => iprop(True))) $$ [] [HΦ]
  · iframe Hc
    imod close_au cn s $$ Hi with ⟨%st, %dd, Hst, Hdd, Hcl⟩
    imodintro
    iexists st, dd
    iframe Hst Hdd
    iintro %res %st' %d' %Hd Hst Hdd
    imod Hcl $$ %res %st' %d' %Hd Hst Hdd with -
    imodintro
    itrivial
  · inext
    iintro %err -
    iapply HΦ; itrivial

/-- `a.String()` of a connection's address (`netAddr`), by `tcpAddrString`. -/
theorem wp_addrString (ra : GoInterface) :
    {{ net.netAddr (GF := GF) ra }}
      (App (App (Val (GoInstruction (MethodResolve net.Addr.ty go!"String"))) (Val #ra)) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  iintro %Φ #Hna HΦ
  iunfold net.netAddr at Hna
  icases Hna with ⟨%pa, %va, %Hra, #Hpa⟩
  subst Hra
  wp_auto
  wp_apply tcpAddrString pa va $$ [$Hpa] as %s -
  iapply HΦ; itrivial

/-- What a client connection's stream (`repDialP`) holds is a prefix of the client's proposal. -/
theorem proto_client (γ : EpNames) (a : GoString) (cid : Nat) (c : w64) (i : KvI) (S : List w8) :
    protoPrefix (GF := GF) (repDialP γ a) cid S -∗ clientConn γ cid c i -∗
      ⌜S <+: proposeBytes c i⌝ := by
  iintro Hp #Hcc
  unfold protoPrefix
  icases Hp with (%H | ⟨%ext, %Hext, #HP⟩)
  · subst H; ipureintro; exact List.nil_prefix
  unfold repDialP
  icases HP with (%He | ⟨%rl, #Hrl, #HP⟩)
  · subst He
    ipureintro; rw [List.prefix_nil.mp Hext]; exact List.nil_prefix
  unfold clientConn
  icases Hcc with ⟨-, #Hrole, -⟩
  ihave %Heq := roleElem_agree $$ Hrole Hrl
  subst Heq
  simp only
  unfold clientDialOk
  icases HP with ⟨-, %Hp⟩
  ipureintro
  exact Hext.trans Hp

/-- A client connection's reader's stream fact (`bufio.ownBufReader_fact` at `prRd`). -/
theorem prRd_fact {br pr t : Loc} {cid : Nat} {eof la ra ed : GoInterface} {P : Proto GF}
    {first R : List w8} :
    rdOwn br (prRd pr t cid eof la ra ed P first) R ⊢
      rdOwn br (prRd pr t cid eof la ra ed P first) R ∗ ▷ protoPrefix P cid R :=
  EtcdGrove.bufio.ownBufReader_fact _ _ _ _ _ _ _ (prRd pr t cid eof la ra ed P first).F_of
    (prRd pr t cid eof la ra ed P first).F_pre

/-- What a client connection's reader returned is a prefix of the client's proposal (a step
later). -/
theorem rd_client (γ : EpNames) (a : GoString) (br pr t : Loc) (cid : Nat) (eof la ra ed : GoInterface)
    (c : w64) (i : KvI) (first R : List w8) :
    rdOwn (GF := GF) br (prRd pr t cid eof la ra ed (repDialP γ a) first) R -∗ clientConn γ cid c i -∗
      rdOwn br (prRd pr t cid eof la ra ed (repDialP γ a) first) R ∗ ▷ ⌜R <+: proposeBytes c i⌝ := by
  iintro Hr #Hcc
  ihave ⟨Hr, #Hp⟩ := prRd_fact $$ Hr
  iframe Hr
  inext
  iapply proto_client $$ Hp Hcc

/-- `rd_client` on the reader's unfolded form (what `Reader.ReadByte`'s spec returns). -/
theorem rd_clientU (γ : EpNames) (a : GoString) (br pr t : Loc) (cid : Nat) (eof la ra ed : GoInterface)
    (c : w64) (i : KvI) (first R : List w8) :
    EtcdGrove.bufio.ownBufReader (GF := GF) br (prIface pr) (fun _ m => 0 < m)
        (prI pr (GoInterface.ok (net.connIface t)) cid (repDialP γ a) first) (net.connReadE eof la ra ed) R -∗
      clientConn γ cid c i -∗
      EtcdGrove.bufio.ownBufReader br (prIface pr) (fun _ m => 0 < m)
        (prI pr (GoInterface.ok (net.connIface t)) cid (repDialP γ a) first) (net.connReadE eof la ra ed) R ∗
        ▷ ⌜R <+: proposeBytes c i⌝ :=
  rd_client γ a br pr t cid eof la ra ed c i first R

theorem cmdOf_wf (i : KvI) (h : inPre i) : cmdWf (cmdOf i) := by
  cases i with
  | get k => simp [cmdWf, cmdOf]
  | put k v => simp only [cmdWf, cmdOf]; have := h.2.2; omega
  | scan k n => simp [cmdWf, cmdOf, u64Le_length]

/-- The client's stream after the `PROPOSE` tag continues with its `Propose`. -/
theorem client_nextIs (γ : EpNames) (a : GoString) (pr t : Loc) (cid : Nat) (eof la ra ed : GoInterface)
    (c : w64) (i : KvI) (first : List w8) :
    clientConn (GF := GF) γ cid c i ⊢
      nextIs (prRd pr t cid eof la ra ed (repDialP γ a) first) [proposeTag] ProposeV.enc (fun p => cmdWf p.cmd) := by
  iintro #Hcc
  ihave #Hcc' := Hcc
  iunfold clientConn at Hcc'
  icases Hcc' with ⟨%Hpre, -⟩
  unfold nextIs
  imodintro
  iintro %S #Hp
  simp only [prRd]
  inext
  ihave %Hp := proto_client $$ Hp Hcc
  ipureintro
  intro hS
  refine ⟨⟨W32 0, W32 (uint.Z c), cmdOf i, W64 0⟩, [], cmdOf_wf i Hpre, ?_⟩
  obtain ⟨t, ht⟩ := Hp
  unfold proposeBytes at ht
  obtain ⟨u, hu⟩ := hS
  subst hu
  simp only [List.length_singleton, List.drop_one, List.tail_cons, List.cons_append,
    List.nil_append, List.singleton_append, List.append_nil]
  simp only [List.cons_append, List.nil_append, List.singleton_append, List.cons.injEq] at ht
  exact ⟨t, ht.2⟩

theorem replica.Replica.clientListener.spec_holds (hPrintln : dlog.Logger.Println.spec (GF := GF))
    (hIsProxy : config.ProxyInfo.IsProxy.spec (GF := GF)) (hPU : replica.defs.Propose.Unmarshal.spec (GF := GF)) :
    replica.Replica.clientListener.spec (GF := GF) := by
  intro γ r id L p Rext conn cid c i fsl first t la ra ed eof
  wp_start as ⟨#Hrun, #Hci, Hsend, Hrecv, Hop, #Hcc, %Hfirst, Hfsl⟩
  ihave #Hci' := Hci
  iunfold connIn at Hci'
  icases Hci' with ⟨%Hcv, ⟨%a, #Hca⟩, #Hed, #Heof⟩
  subst Hcv
  ihave #Hca' := Hca
  iunfold net.connAt at Hca'
  icases Hca' with ⟨%nw, -, -, -, #Hna, -⟩
  ihave #Hcis := sendTok_connIs cid true _ [] $$ Hsend
  unfold fwRun0
  icases Hrun with ⟨#Hro, #Hmu⟩
  ihave #Hro' := fwRO_def $$ Hro
  iunfold fwRODef at Hro'
  icases Hro' with ⟨#HLog, #HLogv, #HN, -, #HId, #HAlias, -, -, #HPeers, #HReaders, #HWriters,
    #HCW, #HCfg, ⟨%cfg, #Hcfg, %Hpx⟩, #Hproxy, #HAlive, -, #HRPC, -, -, -, #HShut, #HPC, -, -, -,
    #HLRead, -, #HEwma, #HLat, #HDt, %HL, #HLf, #HCI, ⟨%γp, #Hpc, -⟩, -⟩
  wp_auto
  wp_alloc pr as Hpr
  iStructNamedPrefix Hpr "pr_"
  ipersist pr_conn
  wp_auto
  ihave #Hrdok := prefixReader_readerOk EpNetDeps.connRead pr t cid a la ra eof ed
    (repDialP γ (L.getD id [])) first $$ [Hca Heof Hed]
  · iframe #; iPkgInit
  ihave HrL := recvTok_L cid true _ first $$ Hrecv
  wp_apply EpBufioDeps.newReaderOk (prIface pr)
    (fun _ m => 0 < m) (prI pr (interface.ok (net.connIface t)) cid (repDialP γ (L.getD id [])) first)
    (net.connReadE eof la ra ed) [] $$ [pr_first Hfsl HrL] as %br Hbr
  · isplitr
    · ipureintro
      simp only [prIface, ne_eq, go.GoType.PointerType.injEq]
      unfold replica.prefixReader.ty _root_.Perennial.bufio.Reader.ty; simp
    isplitr
    · iPkgInit
    iframe Hrdok
    isplitr
    · iapply EtcdGrove.bufio.preUpTo_trivial
    unfold prI
    iexists fsl, 0, []
    simp only [List.drop_zero, List.append_nil, List.take_zero]
    iframe; iframe #
    ipureintro; simp
  ihave #Hwrok := net.conn_streamWriterOk EpNetDeps.connWrite t cid true a la ra ed
    (repAccP γ (L.getD id [])) (repAccP_ppc γ _) $$ [Hca Hed]
  · iframe #
  wp_apply EpBufioDeps.newWriter (net.connIface t)
    _ _ _ [] $$ [Hsend] as %bw Hbw
  · isplitr
    · ipureintro
      simp only [net.connIface, ne_eq, go.GoType.PointerType.injEq]
      unfold net.TCPConn.ty _root_.Perennial.bufio.Writer.ty; simp
    isplitr
    · iPkgInit
    iframe Hwrok Hsend
    imodintro; unfold repAccP; ileft; ipureintro; rfl
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  wp_apply EpNetDeps.connRemoteAddr t cid true a la _ $$ [$Hca]
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
  wp_auto
  isplitr
  · ipureintro; rfl
  iintro %sl_ptr ⟨-, -⟩
  wp_auto
  wp_apply wp_rPrintln hPrintln γ r id L p $$ [$Hro]
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked $HR]
  wp_apply EpNetDeps.connRemoteAddr t cid true a la _ $$ [$Hca]
  ihave #Hna' := Hna
  iunfold net.netAddr at Hna'
  icases Hna' with ⟨%pa, %va, %Hra, #Hpa⟩
  rw [Hra]
  wp_auto
  wp_apply tcpAddrString pa va $$ [$Hpa] as %s0 -
  rw [← Hra]
  wp_apply (strings.wp_Split s0 go!":" (by decide)) as %ssl ⟨Hssl, -⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hssl
  have hne := strings.split_ne_nil s0 go!":"
  obtain ⟨a0, as0, has⟩ : ∃ a0 as0, strings.split s0 go!":" = a0 :: as0 := by
    cases h : strings.split s0 go!":" with
    | nil => exact absurd h hne
    | cons a t => exact ⟨a, t, rfl⟩
  rw [has] at Hsl
  rw [has]
  have hpos : 0 < sint.Z ssl.len := by
    have h1 : ((sint.nat ssl.len : Nat) : Int) = sint.Z ssl.len := by
      first | exact Int.toNat_of_nonneg Hsl.2 | (simp [sint.nat]; omega) | word
    have h2 := Hsl.1; simp only [List.length_cons] at h2; omega
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ssl.len by
    rw [show sint.Z (W64 0) = 0 by decide]; omega)]
  wp_apply wp_load_slice_index ssl (sint.Z (W64 0)) (a0 :: as0) (DFrac.own 1) a0 (by decide)
    $$ [Hssl] as Hssl
  · iframe; ipureintro; rfl
  iStructNamed Hcfg
  rw [Hpx]
  wp_auto
  wp_apply (hIsProxy p.proxy p.aliasStr a0) $$ [$Hproxy]
  -- `mutex := new(sync.Mutex)` (fork workaround MUTEX-LIT): allocated by `wp_auto`
  wp_apply (wp_WaitDuration_nil a0)
  wp_apply (wp_NewDelayProposeChan_zero p.pchan) as %dc ⟨%lc, Hdc⟩
  ipersist Hdc
  iclear Hssl
  ipersist r
  ipersist conn
  ipersist reader
  ipersist writer
  ipersist addr
  ipersist isProxy
  ipersist mutex
  ipersist dchan
  ihave HI : (∃ (e : GoInterface) (mt : w8),
      "err" ∷ err_ptr ↦ e ∗ "msgType" ∷ msgType_ptr ↦ mt ∗
      "Hst" ∷ (⌜e ≠ interface.nil⌝ ∨ (⌜e = interface.nil⌝ ∗
        ((rdOwn br (prRd pr t cid eof la ra ed (repDialP γ (L.getD id [])) first) [] ∗ opTok γ cid ∗
          wrOwn bw (connWr t cid true la ra ed (repAccP γ (L.getD id [])) (repAccP_ppc γ _) 4096) [] [] interface.nil) ∨
         rdOwn br (prRd pr t cid eof la ra ed (repDialP γ (L.getD id [])) first) (proposeBytes c i)))) : IProp GF)
      $$ [err msgType Hbr Hop Hbw]
  · iexists _, _; iframe; iright; isplitr
    · ipureintro; rfl
    ileft; simp only [rdOwn, wrOwn, prRd, connWr]; iframe
  wp_for HI
  icases Hst with (%He | ⟨%He, Hph⟩)
  · -- an error: the loop ends
    cases e with
    | nil => exact absurd rfl He
    | ok ei =>
    wp_auto
    wp_if_destruct
    · exfalso; simp only [goose_wp_simp_extra, goose_wp_simp] at Hif
    try simp only [decide_true, ↓reduceIte]
    wp_apply wp_connClose t cid true a la _ $$ [$Hca $Hcis] as %ce -
    wp_apply EpNetDeps.connRemoteAddr t cid true a la _ $$ [$Hca]
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.any)
    wp_auto
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr2 ⟨-, -⟩
    wp_auto
    wp_apply wp_rPrintln hPrintln γ r id L p $$ [$Hro]
    iapply HΦ; itrivial
  subst He
  wp_auto
  wp_if_destruct
  rotate_left
  · exfalso; simp only [goose_wp_simp_extra, goose_wp_simp] at Hif
  icases Hph with (⟨Hbr, Hop, Hbw⟩ | Hbr)
  rotate_left
  · -- after the proposal: no more bytes can come
    try simp only [decide_true, ↓reduceIte]
    wp_apply EpBufioDeps.readByte br _ _ _ _ _ $$ [$Hbr] as %b %e1 Hrb
    icases Hrb with (⟨%He1, Hbr⟩ | ⟨%He1, #Herr, -, Hbr⟩)
    · ihave ⟨-, Hp⟩ := rd_clientU γ _ br pr t cid eof la ra ed c i first _ $$ Hbr Hcc
      imod Hp with %Hp
      exfalso
      have := Hp.length_le
      simp at this; omega
    cases e1 with
    | nil => exact absurd rfl He1
    | ok ei =>
    wp_auto
    wp_for_post
    try simp only [decide_true, ↓reduceIte]
    wp_apply wp_connClose t cid true a la _ $$ [$Hca $Hcis] as %ce -
    wp_apply EpNetDeps.connRemoteAddr t cid true a la _ $$ [$Hca]
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.any)
    wp_auto
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr2 ⟨-, -⟩
    wp_auto
    wp_apply wp_rPrintln hPrintln γ r id L p $$ [$Hro]
    iapply HΦ; itrivial
  -- the first message: the proposal
  try simp only [decide_true, ↓reduceIte]
  wp_apply EpBufioDeps.readByte br _ _ _ _ _ $$ [$Hbr] as %b %e1 Hrb
  icases Hrb with (⟨%He1, Hbr⟩ | ⟨%He1, #Herr, -, Hbr⟩)
  rotate_left
  · cases e1 with
    | nil => exact absurd rfl He1
    | ok ei =>
    wp_auto
    wp_for_post
    try simp only [decide_true, ↓reduceIte]
    wp_apply wp_connClose t cid true a la _ $$ [$Hca $Hcis] as %ce -
    wp_apply EpNetDeps.connRemoteAddr t cid true a la _ $$ [$Hca]
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.any)
    wp_auto
    isplitr
    · ipureintro; rfl
    iintro %sl_ptr2 ⟨-, -⟩
    wp_auto
    wp_apply wp_rPrintln hPrintln γ r id L p $$ [$Hro]
    iapply HΦ; itrivial
  subst He1
  ihave ⟨Hbr, Hb⟩ := rd_clientU γ _ br pr t cid eof la ra ed c i first _ $$ Hbr Hcc
  imod Hb with %Hb
  have hb : b = proposeTag := by
    obtain ⟨t, ht⟩ := Hb
    unfold proposeBytes at ht
    simp at ht
    exact ht.1
  subst hb
  wp_auto
  ihave #Hnx := client_nextIs γ (L.getD id []) pr t cid eof la ra ed c i first $$ Hcc
  rw [show interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br = brIface br from rfl]
  simp only [List.nil_append]
  wp_apply (hPU _ _ br (prRd pr t cid eof la ra ed (repDialP γ (L.getD id [])) first) _) $$ [Hbr $Hnx «$r0»] as %err2 Hres
  · simp only [rdOwn, prRd]; iframe
  icases Hres with (⟨%He2, %v, %Hv, Hbr, Hpro⟩ | ⟨%He2, %data, Hbr, Hpro⟩)
  rotate_left
  · -- the proposal could not be read: the loop ends at its condition
    cases err2 with
    | nil => exact absurd rfl He2
    | ok ei =>
    wp_auto
    wp_for_post
    iframe
    iexists GoInterface.ok ei, _
    iframe
    ileft; ipureintro; exact He2
  subst He2
  -- the proposal read is the client's
  ihave ⟨Hbr, Hpv⟩ := rd_client γ _ br pr t cid eof la ra ed c i first _ $$ Hbr Hcc
  imod Hpv with %Hpv
  ihave #Hcc' := Hcc
  iunfold clientConn at Hcc'
  icases Hcc' with ⟨%Hpre, #Hrole, -⟩
  have hv : v.enc <+: encPropose (W32 0) (W32 (uint.Z c)) (cmdOf i) (W64 0) := by
    obtain ⟨t, ht⟩ := Hpv
    unfold proposeBytes at ht
    simp only [List.cons_append, List.cons.injEq, true_and] at ht
    exact ⟨t, ht⟩
  obtain ⟨hv1, hv2, hv3, hv4⟩ := encPropose_prefix_eq _ _ _ _ _ _ _ _ Hv (cmdOf_wf i Hpre) hv
  unfold ownPropose
  icases Hpro with ⟨%cv, Hpp, #Hcmd⟩
  rw [hv1, hv2, hv3, hv4]
  ipersist Hpp
  ihave #Hpp' := Hpp
  iStructNamedPrefix Hpp' "pp_"
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold fwLockInv at HR
  icases HR with ⟨Hcore, HRext⟩
  rw [fwCore_unseal]
  iunfold fwCoreDef at Hcore
  icases Hcore with ⟨%ns, %CWm, %CW, %RT, %sm, #Hn, #Hi1, #Hi2, Hp, Hr, Hcwm, HCW, HRT, %HCR, Hcs, Hsm⟩
  wp_apply (wp_mapInsert go.int32 p.cwriters CWm (W32 (uint.Z c)) bw) $$ [$Hcwm] as Hcwm
  -- the fresh writer is not registered yet
  have hcwn : CW.lookup bw = none ∨ ∃ cid', CW.lookup bw = some cid' := by
    cases h : CW.lookup bw with
    | none => exact Or.inl rfl
    | some x => exact Or.inr ⟨x, rfl⟩
  rcases hcwn with hcwn | ⟨cid', hcw'⟩
  rotate_left
  · iexfalso
    icases (BigSepM.bigSepM_lookup_acc (show get? CW bw = some cid' from hcw')).1 $$ Hcs with ⟨Hs, -⟩
    unfold clientSlotX
    icases Hs with ⟨%c2, %s2, %p2, %e2, %t2, %la2, %ra2, %ed2, %eof2, -, Hw2, -⟩
    iapply EtcdGrove.bufio.ownBufWriter_excl $$ [$Hbw $Hw2]
  have hrtn : RT.lookup bw = none := by
    have := HCR bw
    rw [hcwn] at this
    cases h : RT.lookup bw with
    | none => rfl
    | some _ => rw [h] at this; simp at this
  imod (ghost_map_insert_persist bw cid hcwn) $$ HCW with ⟨HCW, #Hcwe⟩
  imod (ghost_map_insert bw () hrtn) $$ HRT with ⟨HRT, Hrte⟩
  ihave Hcs := (BigSepM.bigSepM_insert (show get? CW bw = none from hcwn)).2 $$ [Hcs Hbw]
  · iframe Hcs
    unfold clientSlotX
    iexists _, [], [], interface.nil, t, la, ra, ed, eof
    iframe Hci Hbw
    isplitr
    · ileft; ipureintro; rfl
    iexists c, i; iexact Hrole
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcwm HCW HRT Hcs Hsm Hp Hr HRext]
  · unfold fwLockInv
    rw [fwCore_unseal]
    unfold fwCoreDef
    iframe
    inext
    iframe; iframe #
    ipureintro
    intro w
    show ((<[bw := cid]> CW) !! w).isSome = ((<[bw := ()]> RT) !! w).isSome
    by_cases hw : bw = w
    · subst hw; rw [GMap.lookup_insert, GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ hw, GMap.lookup_insert_ne _ _ hw]; exact HCR w
  ihave #Hpc' := pp_Command
  iStructNamedPrefix Hpc' "cmd_"
  wp_auto
  ipersist «$a0»
  wp_apply (wp_DelayProposeChan_Write_zero dc p.pchan lc _ γp (proposal γ id))
    $$ [Hop Hrte]
  · iframe #
    unfold proposal
    rw [clientWriter_unseal, replyTok_unseal]
    unfold clientWriterDef replyTokDef
    iexists _, bw, _, false, a0, cid, c, i, cv
    iframe; iframe #
  have hR : [proposeTag] ++ v.enc = proposeBytes c i := by
    unfold ProposeV.enc proposeBytes; rw [hv1, hv2, hv3, hv4]
  rw [hR]
  wp_for_post
  iframe
  iexists GoInterface.nil, _
  iframe
  iright
  isplitr
  · ipureintro; rfl
  iright; iexact Hbr

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
