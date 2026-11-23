/-
`Op`'s proof (`OpDefs.lean`: `Op.spec`), from the specs of its callees: the kit's wire
(`state.NIL`, `defs.Propose.Marshal`, `defs.ProposeReplyTS.Unmarshal`), Net's
(`net.DialTimeout`, `Conn.Read`/`Write`/`Close`) and dsv-bufio's (`NewWriter`, `NewReader`,
`Writer.WriteByte`, `Writer.Flush`). Ported from the lab's
`Epaxos/Proof/examples/epaxosnet/OpCore.lean` (`wp_Op_core`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.OpDefs
public import Net.Spec.net.DialTimeout
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Spec.bufio.NewWriter
public import Spec.bufio.NewReaderOk
public import Spec.bufio.Writer__WriteByte
public import Spec.bufio.Writer__Flush
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Perennial.Proof.encoding.binary.Results
public import Perennial.Proof.io.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
  github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace examples.epaxosnet

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics] [π : NetProtoGS]
variable [examples.epaxosnet.Assumptions] [field_sem : net.FieldAssumptions]

/-- `Close()` of a connection whose outcome nobody keeps (`net.Conn.Close.spec` by `close_au`;
`replica/ClientListener.lean`'s `wp_connClose`). -/
theorem wp_connClose (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    {{ net.connAt (GF := GF) t cn s a la ra ∗ connIs (Gg := hG.goose_globalGS) cn }}
      (App (Val #(methods (go.GoType.PointerType net.TCPConn.ty) go!"Close" #t)) (Val #()))
    {{ (err : GoInterface), RET #err; True }} := by
  iintro %Φ ⟨#Hc, #Hi⟩ HΦ
  iapply (wp_Close t cn s a la ra (fun _ => iprop(True))) $$ [] [HΦ]
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

theorem Op.wp_proof
    (wp_NIL : state.NIL.spec (GF := GF))
    (wp_Marshal : replica.defs.Propose.Marshal.spec (GF := GF))
    (wp_Unmarshal : replica.defs.ProposeReplyTS.Unmarshal.spec (GF := GF))
    (wp_DialTimeout : net.DialTimeout.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_NewWriter : EtcdGrove.bufio.NewWriter.spec (GF := GF))
    (wp_NewReader : EtcdGrove.bufio.NewReader.specOk (GF := GF))
    (wp_WriteByte : EtcdGrove.bufio.Writer.WriteByte.spec (GF := GF))
    (wp_Flush : EtcdGrove.bufio.Writer.Flush.spec (GF := GF)) :
    Op.spec (GF := GF) := by
  intro γ sl c i Ψ hpre hc
  unfold state.NIL.spec at wp_NIL
  unfold replica.defs.Propose.Marshal.spec marshalTriple at wp_Marshal
  unfold replica.defs.ProposeReplyTS.Unmarshal.spec unmarshalTriple at wp_Unmarshal
  simp only [bwIface] at wp_Marshal
  simp only [brIface] at wp_Unmarshal
  wp_start as ⟨#Hsl, #Hinvs, HU⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  obtain ⟨hi0, hi6, hia, hir⟩ := opAddr_idx c
  have hlen6 : sint.Z sl.len = 6 := by
    have h1 : serverAddrs.length = sint.nat sl.len := Hlen.1
    have : serverAddrs.length = 6 := rfl
    have h2 := Hlen.2
    word
  rw [if_pos ⟨hi0, by omega⟩]
  wp_apply wp_load_slice_index sl _ serverAddrs _ (opAddr c) hi0 $$ [Hsl] as -
  · iframe #; ipureintro; exact hia
  unfold clientInvs
  icases Hinvs with ⟨#Haps, #Hrole⟩
  ihave #Hap := BigSepL.bigSepL_lookup hir $$ Haps
  ihave %Hok := addrTok_ok (opAddr c) $$ [Hap]
  · iapply addrProto_tok $$ Hap
  ihave #Hnet : (isPkgInit (PROP := IProp GF) pkg_id.net) $$ []
  · iPkgInit
  ihave #Hni : net.isInit $$ []
  · with_unfolding_all iapply isPkgInit_access (PROP := IProp GF) pkg_id.net $$ Hnet
  icases Hni with ⟨-, -, %etl, #Het⟩
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  ihave ⟨%ed, #Hed⟩ := github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll $$ Hpoll
  wp_apply wp_DialTimeout go!"tcp" net.tcpNet_tcp (opAddr c) _ _ ed iprop(True)
      (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (repDialP γ (opAddr c))
        (repAccP γ (opAddr c)) [] [] ∗ connFresh (Gg := hG.goose_globalGS) cn false)) $$ []
    as %cv %err (⟨%Herr, %cid, #Hcv, ⟨Hend, Hfr⟩⟩ | ⟨-, %x, %e, -, #Herr, -⟩)
  · iframe Het Hed
    isplitr
    · ipureintro; exact Hok
    isplit
    · itrivial
    · iapply dial_au (opAddr c) (repDialP γ (opAddr c)) (repAccP γ (opAddr c)) $$ Hap
  rotate_left
  · iunfold net.opErr at Herr
    icases Herr with ⟨%pe, %nw, ⟨%Herr, -⟩, -⟩
    subst Herr
    wp_auto
    iapply HΦ
    ileft; ipureintro; rfl
  subst Herr
  wp_auto
  wp_apply wp_NIL as %nl Hnl
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ x_ptr ↦ inOf i ∗
      ∃ cv : state.Command, cmd_ptr ↦ cv ∗ |==> cmdOk cv (cmdOf i)))) $$ [x cmd Hnl]
  · cases i with
    | get k =>
      simp only [inOf]
      wp_auto
      ihave Hnl := ownSlice_persist _ _ _ $$ Hnl
      isplitr
      · ipureintro; rfl
      iframe x
      iexists _
      iframe cmd
      imod Hnl
      icases Hnl with #Hnl
      imodintro
      unfold cmdOk cmdOf
      iframe #
      ipureintro; simp [opGET]
    | put k v =>
      simp only [inOf]
      wp_auto
      wp_apply +noauto wp_string_to_bytes as %sb ⟨Hsb, -⟩
      ihave Hsb := ownSlice_persist _ _ _ $$ Hsb
      wp_auto
      isplitr
      · ipureintro; rfl
      iframe x
      iexists _
      iframe cmd
      imod Hsb
      icases Hsb with #Hsb
      imodintro
      unfold cmdOk cmdOf
      iframe #
      ipureintro; simp [opPUT]
    | scan k n =>
      simp only [inOf]
      wp_auto
      wp_apply (wp_slice_make2 (V := w8)) as %bs ⟨Hbs, -⟩
      · ipureintro; decide
      ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
      · iPkgInit
      wp_apply encoding.binary.wp_LittleEndian_PutUint64 bs (List.replicate 8 (zero_val w8)) []
        n rfl $$ [Hbs] as Hbs
      · rw [List.append_nil]; iframe Hbs
      rw [List.append_nil]
      ihave Hbs := ownSlice_persist _ _ _ $$ Hbs
      isplitr
      · ipureintro; rfl
      iframe x
      iexists _
      iframe cmd
      imod Hbs
      icases Hbs with #Hbs
      imodintro
      unfold cmdOk cmdOf
      iframe #
      ipureintro; simp [opSCAN]
  iintro %v ⟨%Hv, x, %cv, cmd, Hcmd⟩
  imod Hcmd
  icases Hcmd with #Hcmd
  subst Hv
  wp_auto
  -- register the connection as the op's, depositing the update in its escrow
  ihave HU := opU_shape γ i Ψ $$ HU
  ihave Hreg := escrow_register γ ⊤ cid c i _ CoPset.subseteq_top $$ %hpre Hrole Hfr HU
  iapply fupd_wp
  imod Hreg with ⟨#Hconn, Hclaim⟩
  imodintro
  iunfold net.isConn at Hcv
  icases Hcv with ⟨%t, %la, %ra, %Hct, #Hca⟩
  subst Hct
  iunfold connEnd at Hend
  icases Hend with ⟨Hs, Hr⟩
  ihave #Hcis := sendTok_connIs cid false _ [] $$ Hs
  ihave #Hwok := net.conn_streamWriterOk wp_Write t cid false (opAddr c) la ra ed
    (repDialP γ (opAddr c)) (repDialP_ppc γ _) $$ [Hca Hed]
  · iframe #
  have hci : interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t =
      GoInterface.ok (net.connIface t) := rfl
  rw [hci]
  wp_apply wp_NewWriter (net.connIface t) _ _ _ [] $$ [Hs] as %bw Hbw
  · isplitr
    · ipureintro
      simp only [net.connIface, ne_eq, go.GoType.PointerType.injEq]
      unfold net.TCPConn.ty _root_.Perennial.bufio.Writer.ty; simp
    isplitr
    · iPkgInit
    iframe Hwok Hs
    imodintro; unfold repDialP; ileft; ipureintro; rfl
  wp_apply wp_WriteByte bw _ _ _ _ _ [] [] _ (W8 0) $$ [Hbw] as %e1 ⟨%s1, %p1, %Hwb, Hbw⟩
  · iframe Hbw
    iintro %_ !>
    iapply clientDial_ok γ (opAddr c) cid c i _ (by simp [proposeBytes, proposeTag]) $$ Hconn
  let pv : ProposeV := ⟨W32 0, W32 (uint.Z c), cmdOf i, W64 0⟩
  ihave Hp : ownPropose p_ptr pv.cmdId pv.clientId pv.cmd pv.ts (DFrac.own 1) $$ [p]
  · unfold ownPropose; iexists cv; iframe p; iframe #
  ihave #Hdefs : pkgInit_defs (GF := GF) $$ []
  · iPkgInit
  wp_apply wp_Marshal p_ptr (DFrac.own 1) pv bw
      (connWr t cid false la ra ed (repDialP γ (opAddr c)) (repDialP_ppc γ _) 4096) s1 p1 e1
      $$ [Hbw Hp] as ⟨Hp, %s2, %p2, %e2, %Hws, Hbw⟩
  · simp only [wrOwn, connWr]
    iframe Hbw Hp
    iintro %He1 !>
    have hs : s1 ++ p1 ++ pv.enc = proposeBytes c i := by
      rw [Hwb.2.1 He1]; rfl
    rw [hs]
    iapply clientDial_ok γ (opAddr c) cid c i _ (List.prefix_refl _) $$ Hconn
  simp only [wrOwn, connWr]
  wp_apply wp_Flush bw _ _ _ _ _ s2 p2 e2 $$ [$Hbw] as %e3 ⟨%k3, %Hk3, Hbw⟩
  cases e3 with
  | ok ei =>
    wp_auto
    wp_apply wp_connClose wp_Close t cid false (opAddr c) la ra $$ [$Hca $Hcis] as %e4 -
    iapply HΦ
    ileft; ipureintro; rfl
  | nil =>
  wp_auto
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hn := io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  ihave #Hrdok := net.conn_readerOk wp_Read t cid false (opAddr c) la ra _ ed
    (repAccP γ (opAddr c)) $$ [Hio Hca Heof Hed]
  · iframe #
  ihave HrL := recvTok_L cid false _ [] $$ Hr
  wp_apply wp_NewReader (net.connIface t) (fun _ m => 0 < m)
    (recvTokL (Gg := hG.goose_globalGS) cid false (repAccP γ (opAddr c)))
    (net.connReadE _ la ra ed) [] $$ [HrL] as %br Hbr
  · isplitr
    · ipureintro
      simp only [net.connIface, ne_eq, go.GoType.PointerType.injEq]
      unfold net.TCPConn.ty _root_.Perennial.bufio.Reader.ty; simp
    isplitr
    · iPkgInit
    iframe Hrdok HrL
    iapply EtcdGrove.bufio.preUpTo_trivial
  ihave #Hnx := reply_nextIs γ (opAddr c) t cid c i
    (interface.mkOk errors.errorString.ty.PointerType #eofl) la ra ed $$ Hconn
  wp_apply (wp_Unmarshal «$r0_ptr» _ br
      (connRd t cid false (interface.mkOk errors.errorString.ty.PointerType #eofl) la ra ed
        (repAccP γ (opAddr c))) []) $$ [Hbr «$r0»] as %err2 Hres
  · iframe «$r0» Hnx
    simp only [rdOwn, connRd]
    iexact Hbr
  wp_apply (lc := 1) wp_connClose wp_Close t cid false (opAddr c) la ra $$ [$Hca $Hcis] as %e5 -
  icases Hres with (⟨%He2, %rv, %Hrv, Hr, %rsl, «$r0», Hrsl⟩ | ⟨%He2, -⟩)
  rotate_left
  · cases err2 with
    | nil => exact absurd rfl He2
    | ok ei =>
      wp_auto
      iapply HΦ
      ileft; ipureintro; rfl
  subst He2
  simp only [List.nil_append]
  ihave ⟨Hr, Hf⟩ := reply_read γ (opAddr c) t cid c i _ la ra ed br rv Hrv $$ Hconn Hr
  imod Hf with ⟨%o, #Hfired, %Hro⟩
  obtain ⟨hok, hcid, hval⟩ := Hro
  rcases rv with ⟨rok, rcid, rval, rts⟩
  simp only at hok hcid hval
  subst hok hcid
  iapply fupd_wp
  imod escrow_claim γ ⊤ cid i _ o CoPset.subseteq_top $$ Hclaim Hfired Hlc1 with ⟨HΨ, %Hsh⟩
  imodintro
  cases i with
  | put k v =>
    simp only [outShape] at Hsh
    subst Hsh
    simp only [inOf]
    wp_auto
    iapply HΦ
    iright
    iexists KvsOutput.done
    iframe HΨ
    ipureintro; rfl
  | get k =>
    simp only [outShape] at Hsh
    simp only [inOf]
    wp_auto
    wp_apply wp_bytes_to_string rsl rval (DFrac.own 1) $$ [$Hrsl] as -
    iapply HΦ
    iright
    iexists o
    iframe HΨ
    ipureintro
    simp only [examples.epaxosnet.outOk, outBytes_read o rval (.inl Hsh) hval]
  | scan k n =>
    simp only [outShape] at Hsh
    simp only [inOf]
    wp_auto
    wp_apply wp_bytes_to_string rsl rval (DFrac.own 1) $$ [$Hrsl] as -
    iapply HΦ
    iright
    iexists o
    iframe HΨ
    ipureintro
    simp only [examples.epaxosnet.outOk, outBytes_read o rval (.inr Hsh) hval]

end proof


end examples.epaxosnet

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
