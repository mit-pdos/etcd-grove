/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ClientListener.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`r.clientListener(conn, br)`: P1's classification of an accepted connection, then the client's
proposals off a stream the protocol admits (`sp.client_kind`, `sp.client_code`,
`sp.stream_next`), each handed to `ProposeChan` with its registration.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ClientSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetConn
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WriterExcl
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println
public import Perennial.Spec.strings.Split

-- PORT: lab imports dropped: Harness.Proof.bufio.Net

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions] [config.Assumptions]
variable [bufio.Assumptions] [net.Assumptions] [net.FieldAssumptions] [io.Assumptions] [net.rpc.Assumptions]
  [errors.Assumptions] [dlog.Assumptions] [time.Assumptions]
  [state.Assumptions] [strings.Assumptions] [sync.Assumptions]

set_option goose.wp.extras true

set_option hygiene false in
/-- After the loop: `conn.Close()`, `r.Println("Client down", ...)`. -/
local macro "postloop" : tactic => `(tactic| (
  try wp_pures
  try wp_auto
  wp_apply wp_Close cl0 cid true $$ [Hown] as %e2 -
  · iexact Hown
  try wp_auto
  wp_apply wp_RemoteAddr cl0 cid true $$ [Hown] as %ad3 %Had3
  · iexact Hown
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl3 ⟨-, -⟩
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  wp_apply wp_Println $$ Hquiet
  try wp_auto
  iapply HΦ; itrivial))

theorem replica.Replica.clientListener.wp_proof
    (wp_PUnm : replica.defs.Propose.Unmarshal.spec (GF := netDistGF) (hG := hG))
    (wp_WaitDuration : replica.defs.LatencyTable.WaitDuration.spec (hG := hG))
    (wp_NewDPC : replica.defs.NewDelayProposeChan.spec (hG := hG))
    (wp_DPCWrite : replica.defs.DelayProposeChan.Write.spec (hG := hG))
    (wp_IsProxy : config.ProxyInfo.IsProxy.spec (hG := hG))
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG))
    (wp_RemoteAddr : net.TCPConn.RemoteAddr.spec (GF := netDistGF) (hG := hG))
    (wp_Close : net.TCPConn.Close.spec (GF := netDistGF) (hG := hG))
    (wp_Split : strings.Split.spec (GF := netDistGF) (hG := hG)) :
    replica.Replica.clientListener.spec (hG := hG) := by
  intro r γ γc γm γw N me al cv cid br first hasFirst
  wp_start as ⟨#Hrep, #HAlias, #Hc, Hrd, %Hff, Hsend⟩
  ihave #Hr := Hrep
  iunfold replica.isReplica at Hr
  icases Hr with ⟨%lg, %cfgp, %tbl, %pc, %fr, %nid, %ents, %γpc, %pwsl, %alsl, %latsl,
    %pws, %cwm, #Hlg, #Hquiet, #HN, #HId, #HCfg, #Hplain, #HRPC, #Htbl, #HtOk, #HPC, #Hpcbag,
    #HSd, #HLR, #HDt, #HPW, #Hpws, #HAl, #HLat, #HCW, %Hlens, #Hmu⟩
  -- the writer
  ihave #Hpc := sp.outQ_prefixClosed (γ := γ) (γc := γc) (γm := γm) cid
  ihave #Hpc' : (bufio.prefixClosed (sp.outQ γ γc γm cid) : IProp netDistGF) $$ []
  · unfold bufio.prefixClosed; imodintro; iexact Hpc
  ihave #Hwok := bufio.writerOk_conn cv cid true (sp.outQ γ γc γm) $$ [$Hpkg3 $Hc $Hpc']
  ihave #Hq0 := sp.outQ_nil (γ := γ) (γc := γc) (γm := γm) cid
  wp_auto
  wp_apply bufio.wp_NewWriter cv _ _ [] $$ [$Hpkg2 $Hwok $Hsend $Hq0] as %w Hw
  ihave #Hrdok := bufio.readerOk_conn cv cid true (sp.inP γ γc γm) $$ [$Hpkg3 $Hc]
  try wp_auto
  ihave #Hc2 := Hc
  iunfold net.rpc.connIface at Hc2
  icases Hc2 with ⟨%cl0, %a0, %la0, %ra0, %Hcv, #Hat0, #Hcs0⟩
  ihave #Hown : net.ownTCPConn (GF := netDistGF) cl0 cid true $$ []
  · unfold net.ownTCPConn; iexists a0, la0, ra0; iframe Hat0 Hcs0
  ipersist conn
  ipersist r
  ipersist reader
  try wp_auto
  wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ ∃ fv : w8, first_ptr ↦ fv ∗
      hasFirst_ptr ↦ true ∗ bufio.ownReader br cv (recvTok cid true (sp.inP γ γc γm)) [fv] ∗
      (∃ cl, sp.connKind γ cid (.client cl))) ∨ ⌜v = returnVal #()⌝)) at next
    with [Hrd first hasFirst]
  · cases hasFirst
    · -- the first byte read here (R2 workaround: `ReadByte`, not `Peek`)
      simp only [Bool.false_eq_true, ↓reduceIte] at *
      wp_pures
      wp_auto
      wp_apply bufio.wp_ReadByte br cv _ [] $$ [$Hpkg2 $Hrdok $Hrd] as %c %er Hr
      icases Hr with (⟨%Hen, Hrd⟩ | ⟨%Hen, #Hea, Hrd⟩)
      · subst Hen
        try wp_auto
        wp_if_destruct
        · -- a peer's hello (P1): the connection is not a client's
          subst Hcv
          wp_auto
          wp_apply wp_Close cl0 cid true $$ [$Hpkg3 $Hown] as %e2 -
          iright; ipureintro; rfl
        · -- a client's connection
          icases sp.ownReader_proto br _ cid true _ ([] ++ [c]) $$ Hrd with
            ⟨Hrd, (%Hnil | ⟨%ext, %Hext, #HP⟩)⟩
          · simp at Hnil
          ihave ⟨%cl, #Hk⟩ := sp.client_kind cid ext c (by simpa using Hext) Hif $$ HP
          try wp_auto
          ileft
          isplitr
          · ipureintro; first | rfl | trivial
          iexists c
          iframe
          iexists cl; iexact Hk
      · -- R-F2: a failed first read closes the connection
        rcases er with eo | _
        · subst Hcv
          wp_auto
          wp_apply wp_Close cl0 cid true $$ [$Hpkg3 $Hown] as %e2 -
          iright; ipureintro; rfl
        · exact absurd rfl Hen
    · -- the first byte read by `waitForPeerConnections`
      simp only [↓reduceIte] at *
      have hff : first ≠ W8 0xFF := by simpa using Hff
      try wp_auto
      icases sp.ownReader_proto br _ cid true _ [first] $$ Hrd with
        ⟨Hrd, (%Hnil | ⟨%ext, %Hext, #HP⟩)⟩
      · simp at Hnil
      ihave ⟨%cl, #Hk⟩ := sp.client_kind cid ext first Hext hff $$ HP
      ileft
      isplitr
      · ipureintro; first | rfl | trivial
      iexists first
      iframe
      iexists cl; iexact Hk
  iintro (⟨%Hv, %fv, first, hasFirst, Hrd, Hk0⟩ | %Hv) <;> subst Hv
  rotate_left
  · wp_auto
    iapply HΦ; itrivial
  subst Hcv
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  try wp_auto
  wp_apply wp_RemoteAddr cl0 cid true $$ [$Hown] as %ad %Had
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨-, -⟩
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  wp_apply wp_Println $$ Hquiet
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [Hlocked HR]
  · iframe Hmu Hlocked; try inext; iexact HR
  try wp_auto
  wp_apply wp_RemoteAddr cl0 cid true $$ [$Hown] as %ad2 %Had2
  obtain ⟨xa, rfl⟩ := Had2
  try wp_auto
  wp_apply net.wp_TCPAddr_String xa as %str -
  try wp_auto
  wp_apply wp_Split str [58#8] (by simp) as %spl ⟨Hspl, -⟩
  ihave %Hsplen := ownSlice_len _ _ _ $$ Hspl
  obtain ⟨a0, rest, hsp⟩ : ∃ a0 rest, strings.split str [58#8] = a0 :: rest := by
    cases h : strings.split str [58#8] with
    | nil => exact absurd h (strings.split_ne_nil _ _)
    | cons a0 rest => exact ⟨a0, rest, rfl⟩
  rw [hsp] at Hsplen
  isimp only [hsp] at Hspl
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by
    have h1 : sint.nat spl.len = rest.length + 1 := by simpa using Hsplen.1.symm
    have h0 : sint.Z (W64 0) = 0 := rfl
    have e1 : sint.nat spl.len = (sint.Z spl.len).toNat := rfl
    omega⟩)]
  wp_apply wp_load_slice_index _ _ _ _ a0 (by decide) $$ [Hspl] as Hspl
  · iframe Hspl; ipureintro; rfl
  -- the configuration's ProxyInfo: empty
  iunfold config.plain at Hplain
  icases Hplain with ⟨%cv0, %pi, #Hcfgv, #Hpi, %Hpl⟩
  ihave #Hcfgv' := Hcfgv
  iStructNamed Hcfgv'
  try wp_auto
  wp_apply wp_IsProxy cv0.Proxy' pi al a0 $$ [$Hpi]
  · ipureintro; exact Hpl.2.2.2.2.2.2.1
  try wp_auto
  try wp_auto
  wp_apply wp_WaitDuration
  try wp_auto
  wp_apply wp_NewDPC pc as %dc ⟨%dcv, Hdcv, %Hdcvp⟩
  ipersist Hdcv
  ihave #Hdc : replica.defs.dpcOk dc pc $$ []
  · iunfold replica.defs.dpcOk; iexists dcv; iframe Hdcv; ipureintro; exact Hdcvp
  try wp_auto
  ipersist writer
  ipersist mutex
  ipersist dchan
  ipersist addr
  ipersist isProxy
  ihave HL : (∃ (R : List w8) (done : List sp.Msg) (er : GoInterface) (mt : w8)
      (ko : Option w32) (hf : Bool),
      "err" ∷ err_ptr ↦ er ∗ "msgType" ∷ msgType_ptr ↦ mt ∗ "hasFirst" ∷ hasFirst_ptr ↦ hf ∗
      "Hrd" ∷ bufio.ownReader br (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #cl0)
        (recvTok cid true (sp.inP γ γc γm)) (R ++ if hf then [fv] else []) ∗
      "Hk" ∷ (match ko with
        | none => ⌜False⌝
        | some cl => sp.connKind γ cid (.client cl) ∗
            ⌜er = interface.nil → sp.rdAt (.client cl) done R⌝) ∗
      "Hwr" ∷ (bufio.ownWriter w (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #cl0)
          (sendTok cid true (sp.outQ γ γc γm)) (sp.outQ γ γc γm cid) [] [] interface.nil ∨
        ∃ cl, ⌜ko = some cl⌝ ∗ ghostMapElem γw w DFrac.discard cl) :
      IProp netDistGF) $$ [err msgType hasFirst Hrd Hk0 Hw]
  · icases Hk0 with ⟨%cl, #Hk⟩
    iexists [], [], _, _, some cl, true
    iframe
    isplitr
    · simp only [named]
      iframe Hk
      ipureintro; intro _; exact ⟨by simp [sp.RdKind.head, sp.framesOf], by simp⟩
    ileft; iframe
  ipersist first
  wp_for HL
  try wp_auto
  rcases er with eo | _
  · -- an error: the loop ends
    try wp_auto
    cleanup_bool_decide
    try rw [if_neg (by decide)]
    postloop
  · try wp_auto
    rw [if_pos (decide_eq_true rfl)]
    try wp_auto
    -- the message type: the byte read first (R2 workaround), or the next one
    wp_join (Q := fun v => iprop((⌜v = executeVal⌝ ∗ ∃ c : w8, msgType_ptr ↦ c ∗
        hasFirst_ptr ↦ false ∗ err_ptr ↦ interface.nil ∗
        bufio.ownReader br (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #cl0)
          (recvTok cid true (sp.inP γ γc γm)) (R ++ [c])) ∨ ⌜v = breakVal⌝)) at next
      with [Hrd msgType hasFirst err]
    · cases hf
      · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at *
        try wp_auto
        wp_apply bufio.wp_ReadByte br _ _ R $$ [$Hpkg2 $Hrdok $Hrd] as %c %er2 Hr
        icases Hr with (⟨%Hen, Hrd⟩ | ⟨%Hen, #Hea, Hrd⟩)
        · subst Hen
          try wp_auto
          ileft
          isplitr
          · ipureintro; first | rfl | trivial
          iexists c; iframe
        · rcases er2 with eo | _
          · try wp_auto
            iright; ipureintro; rfl
          · exact absurd rfl Hen
      · simp only [↓reduceIte] at *
        try wp_auto
        ileft
        isplitr
        · ipureintro; first | rfl | trivial
        iexists fv; iframe
    iintro (⟨%Hv, %c, msgType, hasFirst, err, Hrd⟩ | %Hv) <;> subst Hv
    rotate_left
    · try wp_auto
      wp_for_post
      postloop
    try wp_auto
    icases sp.ownReader_proto br _ cid true _ (R ++ [c]) $$ Hrd with
      ⟨Hrd, (%Hnil | ⟨%ext, %Hext, #HP⟩)⟩
    · simp at Hnil
    -- the connection's kind (a client's) and the type byte (PROPOSE)
    ihave ⟨%cl, %done', #Hk1, %Hat1, %Hc0, Hwr⟩ : (∃ (cl : w32) (done' : List sp.Msg),
        sp.connKind γ cid (.client cl) ∗ ⌜sp.rdAt (.client cl) done' R⌝ ∗ ⌜c = W8 0⌝ ∗
        (bufio.ownWriter w (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #cl0)
          (sendTok cid true (sp.outQ γ γc γm)) (sp.outQ γ γc γm cid) [] [] interface.nil ∨
          ghostMapElem γw w DFrac.discard cl) : IProp netDistGF) $$ [Hk Hwr]
    · rcases ko with _ | cl
      · simp only [named]
        icases Hk with %HR0
        exact HR0.elim
      · simp only [named]
        icases Hk with ⟨#Hk, %Hat0⟩
        obtain ⟨hR, hdone⟩ := Hat0 trivial
        ihave %Hc := sp.client_code cid cl ext done c
          (by rw [hR] at Hext; simpa [sp.RdKind.head, List.append_assoc] using Hext)
          (fun d hd => (hdone d hd).1) $$ [$Hk $HP]
        iexists cl, done
        iframe Hk
        isplitr
        · ipureintro; exact ⟨hR, hdone⟩
        isplitr
        · ipureintro; exact Hc
        icases Hwr with (Hwr | ⟨%cl', %Hcl', #Hg⟩)
        · ileft; iexact Hwr
        · cases Hcl'; iright; iexact Hg
    subst Hc0
    obtain ⟨hR, hdone⟩ := Hat1
    wp_if_destruct
    rotate_left
    · exact absurd rfl Hif
    try wp_auto
    ihave #Hrs := bufio.bufioReadsOk br _ _ $$ [$Hpkg2 $Hrdok]
    wp_apply wp_PUnm _ _ _ _ (R ++ [W8 0]) $$ [$Hpkg4 $Hrs $Hrd $«$r0»] as %er3 ⟨%data, Hrd, Hres⟩
    icases Hres with (⟨%Hen, %seq, %cl', %cm, %ts, %vs, %Hdec, Hp, Hvs⟩ | ⟨%Hen, %pv', Hp⟩)
    rotate_left
    · rcases er3 with eo | _
      · try wp_auto
        wp_for_post
        iframe
        iexists _, done', _, _, some cl, false
        simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
        iframe
        isplitl []
        · simp only [named]; iframe Hk1; ipureintro; intro h; cases h
        icases Hwr with (Hwr | #Hg)
        · ileft; iexact Hwr
        · iright; iexists cl; iframe Hg; ipureintro; rfl
      · exact absurd rfl Hen
    subst Hen
    icases sp.ownReader_proto br _ cid true _ (R ++ [W8 0] ++ data) $$ Hrd with
      ⟨Hrd, (%Hnil | ⟨%ext2, %Hext2, #HP2⟩)⟩
    · simp at Hnil
    have hpre : (sp.RdKind.client cl).head ++ sp.framesOf done' ++ W8 0 :: data <+: ext2 := by
      rw [hR] at Hext2; simpa [sp.RdKind.head, List.append_assoc] using Hext2
    ihave ⟨#Hmsg, %Hst⟩ := sp.stream_next (.client cl) cid ext2 done' (W8 0) data
      (.propose seq cl' cm ts) hpre Hdec (fun d hd => (hdone d hd).1) $$ []
    · simp only [sp.RdKind.conn, sp.RdKind.proto]; iframe Hk1 HP2
    have hcl : cl' = cl := Hst.1
    subst cl'
    isimp only [sp.msgOk] at Hmsg
    try wp_auto
    wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
    · iexact Hmu
    iunfold replica.lockInv at HR
    icases HR with ⟨%alive, %lats, Hal, Hlat, %Hl, Hpw, Hcw⟩
    iunfold replica.clientWrs at Hcw
    icases Hcw with ⟨%cw, %ws, Hcwm, Hauth, %Hcwi, Hws⟩
    try wp_auto
    wp_apply (wp_mapInsert (K := w32) (V := Loc)) $$ Hcwm as Hcwm
    -- the writer registered: the clients' writers' invariant again, and its witness
    ihave Hreg : (|==> (replica.clientWrs γ γc γm γw cwm ∗ ghostMapElem γw w DFrac.discard cl) :
        IProp netDistGF) $$ [Hcwm Hauth Hws Hwr]
    · icases Hwr with (Hwr | #Hg)
      · ihave ⟨%Hfr, Hws, Hwr⟩ := clientWrs_fresh γ γc γm γw ws w _ _ _ _ _ _ $$ [Hws Hwr]
        · iframe
        imod ghost_map_insert_persist w cl Hfr $$ Hauth with ⟨Hauth, #Hg⟩
        imodintro
        iframe Hg
        iunfold replica.clientWrs
        iexists _, _
        iframe Hcwm Hauth
        isplitr
        · ipureintro; exact cwInv_fresh cw ws cl w Hcwi Hfr
        iapply (BigSepM.bigSepM_insert (Φ := fun w' cl => sp.wrSt γ γc γm w' (.client cl))
          (m := ws) (i := w) (x := cl) Hfr).2
        iframe Hws
        iunfold sp.wrSt
        iexists _, cid, [], [], interface.nil
        simp only [sp.WrKind.side, sp.WrKind.proto, sp.WrKind.conn, List.append_nil]
        iframe Hc Hk1 Hwok Hwr
        iright
        iunfold sp.wrAt
        iexists []
        isplitr
        · ipureintro; exact ⟨by simp [sp.WrKind.head, sp.framesOf], by simp⟩
        iapply (BigSepL.bigSepL_nil_intro (P := iprop(True))); itrivial
      · ihave %Hlk := ghost_map_lookup $$ Hauth Hg
        imodintro
        iframe Hg
        iunfold replica.clientWrs
        iexists _, ws
        iframe Hcwm Hauth Hws
        ipureintro; exact cwInv_reg cw ws cl w Hcwi Hlk
    imod Hreg with ⟨Hcw, #Hg⟩
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hal Hlat Hpw Hcw]
    · iframe Hmu Hlocked
      try inext
      iunfold replica.lockInv
      iexists alive, lats
      iframe
      ipureintro; exact Hl
    try wp_auto
    ipersist «$a0»
    ipersist Hvs
    ipersist Hp
    wp_apply wp_DPCWrite dc pc γpc (sp.proposeP γ) «$a0_ptr» $$ [Hp Hvs]
    · iframe Hdc Hpcbag
      iunfold sp.proposeP
      iexists _, _, _, _, seq, cl, cm, ts, vs
      iframe «$a0» Hp Hvs Hmsg
      ipureintro; exact Hdec.2.1
    wp_for_post
    iframe
    iexists (R ++ W8 0 :: data), done' ++ [.propose seq cl cm ts], _, _, some cl, false
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
    rw [show R ++ [W8 0] ++ data = R ++ W8 0 :: data by simp]
    iframe
    isplitl []
    · simp only [named]
      iframe Hk1
      ipureintro; intro _
      exact sp.rdAt_snoc ⟨hR, hdone⟩ Hst.2 Hdec.2.1 Hst.1
    iright; iexists cl; iframe Hg; ipureintro; rfl

end proof

end Perennial.github_com.imdea_software.swiftpaxos
