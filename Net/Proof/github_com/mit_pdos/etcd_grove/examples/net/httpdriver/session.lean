/- Lean-first (no Rocq counterpart).

# `session`'s proof

`net.Dial` with `dial_rdl_au` (`drvAddr`'s `addrProto`), the connection registered
(`http_register`: its slots a mono-list, split in halves), the reader `bufio.NewReader` of the
connection's stream (`hcStream`, from `hcSt_init` with one half). The loop's invariant at `i`: `i`
request slots `L` written (`sendTok`, their facts), the reader past the `i` answers `A` read
(`respsWire`), each delimited by its `Content-Length`, the other half of the slots. Each iteration:
`randomRequest`'s `d`, its body saved at a fresh ghost name `τ` (persistent), its slot added
(`ownReader_addSlot`), written (`write_acc`, `reqP_snoc`); `ReadResponse` with the knowledge `drvQ`
of the answer at `i` (`hcSt_law`), `io.ReadAll` of its body to `io.EOF`, `check` (`drvQ_chk`), and
the exit on a `400` (otherwise the answer is a handler's, its wire next in the reader). Every error
leaves the loop; then `Close`.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.session
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.below
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.randomRequest
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.check
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.SessionLemmas
public import Net.Spec.net.Dial
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Conn__Read
public import Spec.bufio.NewReader
public import Net.Spec.net.http.ReadResponse
public import Perennial.Spec.io.ReadAll

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open net.http (HReq HProto Resp RespSlot ReqSlot HdrLine HttpProtoGS)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS] [hπ : HttpProtoGS]

/-! The loop counter's arithmetic. -/

theorem sess_zero : uint.nat (W64 0) = 0 := by word

theorem sess_lt (i n : w64) (h : uint.Z i < uint.Z n) : uint.nat i < uint.nat n := by word

theorem sess_bound (n0 : w64) (h : uint.Z n0 < 4) : uint.nat (W64 1 + n0) ≤ 4 := by word

theorem sess_succ (i n : w64) (h : uint.nat i < uint.nat n) : uint.nat (i + W64 1) = uint.nat i + 1 := by
  word

-- After the loop (or a `break`): `c.Close()`, then the return.
set_option hygiene false in
local macro "close_tac" : tactic => `(tactic| (
  wp_apply wp_Close t cn false addrS la ra (fun _ => iprop(True)) $$ [] as %cerr -
  · iframe Hca
    iapply close_true cn $$ Hci
  iapply HΦ
  itrivial))

theorem session.wp_proof
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_randomRequest : randomRequest.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_ReadLc : net.Conn.Read.specLc (GF := GF) (hG := hG))
    (wp_NewReader : EtcdGrove.bufio.NewReader.spec (GF := GF) (hG := hG))
    (wp_ReadResponse : net.http.ReadResponse.spec_resp (GF := GF) (hG := hG))
    (wp_ReadAll : io.ReadAll.spec (GF := GF) (hG := hG)) :
    session.spec (GF := GF) (hG := hG) := by
  wp_start as ⟨#Hf, #Haddr⟩
  ihave ⟨#Hhenv, #Hio, #Hbufio, ⟨%ed, #Hed⟩, ⟨%eof, #Heof⟩⟩ := drv_env $$ Hpkg
  ihave #Hf' := Hf
  iunfold drvFacts at Hf'
  icases Hf' with ⟨%fr, #Hrg, #Hrf⟩
  iunfold drvAddr at Haddr
  icases Haddr with ⟨#Hap, #Hreg⟩
  ihave %Hok := addrTok_ok $$ [Hap]
  · iapply addrProto_tok $$ Hap
  try wp_auto
  rw [show Addr = #addrS from rfl]
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp addrS iprop(True)
      (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false
        (net.http.httpReqP (Gg := hG.goose_globalGS) drvP)
        (net.http.httpRespP (Gg := hG.goose_globalGS) drvP) [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn false ∗
        rdlTok (Gg := hG.goose_globalGS) cn false false)) $$ [Hap]
    as %c %err (⟨%Herr, %cn, #Hc, Hend, Hfresh, Hrdl⟩ | ⟨-, %x, -, #HE⟩)
  · isplitr
    · ipureintro; exact Hok
    isplit
    · itrivial
    · iapply dial_rdl_au $$ Hap
  · subst Herr
    iunfold net.isConn at Hc
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    iunfold connEnd at Hend
    icases Hend with ⟨Hsend, Hrecv⟩
    ihave #Hci := sendTok_connIs $$ Hsend
    -- the connection registered, its slots' mono-list in halves
    ihave Hr : (|={⊤}=> ∃ γ : GName, net.http.httpConn (Gg := hG.goose_globalGS) cn γ ∗
        monoListAuthOwn γ 1 ([] : List ReqSlot) : IProp GF) $$ [Hfresh]
    · iapply http_register cn $$ [$Hreg $Hfresh]
    imod Hr with ⟨%γ, #Hhc, Hml⟩
    icases (sess_ml_halves γ ([] : List ReqSlot)).1 $$ Hml with ⟨Hml1, Hml2⟩
    -- the reader's stream
    ihave HS0 := hcSt_init cn γ $$ [$Hrecv $Hrdl $Hhc $Hml1]
    imod HS0 with ⟨%γe, HS0⟩
    ihave #Hstream := hcStream wp_ReadLc cn γ γe t la ra ed $$ [$Hio $Hed $Hca]
    ihave #Hstream0 := EtcdGrove.io.readerStreamNE_readerStream _ _ _ $$ Hstream
    ihave #Hbound : (□ ∀ r0, hcSt cn γ γe r0 -∗ ⌜r0.length + 2 ^ 12 < 2 ^ 62⌝ : IProp GF) $$ []
    · imodintro
      iintro %r0 HS
      iapply hcSt_bound $$ HS
    ihave #Hfin : (□ ∀ (r r' : List w8) (e : GoInterface), hcErr γe r e -∗ hcSt cn γ γe r' -∗
        ⌜r <+: r' → r' = r⌝ : IProp GF) $$ []
    · imodintro
      iintro %r %r' %e He HS
      iapply hcErr_final cn γ γe r r' e $$ [$He $HS]
    have hty : (net.connIface t).ty ≠ go.GoType.PointerType _root_.Perennial.bufio.Reader.ty := by
      show go.GoType.PointerType net.TCPConn.ty ≠ _
      simp only [ne_eq, go.GoType.PointerType.injEq]
      unfold net.TCPConn.ty _root_.Perennial.bufio.Reader.ty
      simp
    try wp_auto
    rw [show interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t = GoInterface.ok (net.connIface t)
      from rfl]
    wp_apply wp_NewReader (net.connIface t) (hcSt cn γ γe) (hcErr γe) [] hty
        $$ [$Hbufio $Hstream0 $Hbound $HS0] as %br0 Hb
    try wp_auto
    wp_apply wp_below (W64 4) as %n0 %Hn0
    have hn0 : uint.Z n0 < 4 := Hn0.2 (by decide)
    try wp_auto
    -- the loop
    ihave Hb : EtcdGrove.bufio.ownReader br0 (net.connIface t) (hcSt cn γ γe) (hcErr γe)
        (net.http.respsWire (([] : List Resp).map RespSlot.ans)) $$ [Hb]
    · rw [show net.http.respsWire (([] : List Resp).map RespSlot.ans) = [] from rfl]
      iexact Hb
    ihave Hsend : sendTok (Gg := hG.goose_globalGS) cn false
        (net.http.httpReqP (Gg := hG.goose_globalGS) drvP) (net.http.slotsWire ([] : List ReqSlot))
        $$ [Hsend]
    · rw [show net.http.slotsWire ([] : List ReqSlot) = [] from rfl]
      iexact Hsend
    ihave IH : iprop(∃ (i : w64) (A : List Resp) (L : List ReqSlot),
        "i" ∷ i_ptr ↦ i ∗
        "Hb" ∷ EtcdGrove.bufio.ownReader br0 (net.connIface t) (hcSt cn γ γe) (hcErr γe)
          (net.http.respsWire (A.map RespSlot.ans)) ∗
        "Hml" ∷ monoListAuthOwn γ (1 : Qp).half L ∗
        "Hsend" ∷ sendTok (Gg := hG.goose_globalGS) cn false
          (net.http.httpReqP (Gg := hG.goose_globalGS) drvP) (net.http.slotsWire L) ∗
        "#Hfs" ∷ ([∗list] s ∈ L, net.http.slotFacts drvP s) ∗
        "%Hinv" ∷ ⌜A.length = uint.nat i ∧ L.length = uint.nat i ∧
          (∀ ρ ∈ A, net.http.respOk ρ ∧ ρ.close = false) ∧
          (∀ s ∈ L, net.http.slotOk s ∧ s.isLeft = true) ∧ uint.nat i ≤ uint.nat (W64 1 + n0)⌝)
        $$ [i Hb Hml2 Hsend]
    · iexists W64 0, [], []
      iframe i Hb Hml2 Hsend
      isplitr
      · iapply BigSepL.bigSepL_nil.2
        iempintro
      ipureintro
      rw [sess_zero]
      exact ⟨rfl, rfl, by simp, by simp, Nat.zero_le _⟩
    wp_for IH
    wp_if_destruct
    · -- an iteration
      have hi : uint.nat i < uint.nat (W64 1 + n0) := sess_lt _ _ Hif
      obtain ⟨hA, hLl, hAok, hLok, -⟩ := Hinv
      have hL4 : L.length < 4 := by
        have := sess_bound n0 hn0
        omega
      wp_apply wp_randomRequest as %qv %Hq
      obtain ⟨d, hd, hq⟩ := Hq
      -- the request's body, saved at a fresh ghost name; its slot added
      imod (dghostVar_alloc (GF := GF) d.body) with ⟨%τ, Hτ⟩
      imod dghostVar_persist τ 1 d.body $$ Hτ with #Hτ
      imod ownReader_addSlot br0 (net.connIface t) (hcErr γe) cn γ γe _ L (d.slot τ) hL4
        $$ [$Hb $Hml] with ⟨Hb, Hml⟩
      icases ml_auth_lb γ _ (L ++ [d.slot τ]) $$ Hml with ⟨Hml, #HlbL⟩
      -- the write
      ihave #HP := reqP_snoc cn γ L d hd τ hLok $$ [$Hhc $HlbL $Hfs $Hτ]
      ihave #Hacc := write_acc (Gg := hG.goose_globalGS) cn false
        (net.http.httpReqP (Gg := hG.goose_globalGS) drvP) (net.http.slotsWire L) d.wire $$ HP
      ihave HwP := writeP_init (Gg := hG.goose_globalGS) cn false
        (net.http.httpReqP (Gg := hG.goose_globalGS) drvP) (net.http.slotsWire L) $$ Hsend
      try wp_auto
      wp_apply wp_string_to_bytes qv.raw' as %sl ⟨Hsl, -⟩
      ihave Hsl : sl ↦* d.wire $$ [Hsl]
      · rw [← hq.1]; iexact Hsl
      wp_apply wp_Write t cn false addrS la ra sl d.wire _ ed
          (writeP (Gg := hG.goose_globalGS) cn false
            (net.http.httpReqP (Gg := hG.goose_globalGS) drvP) (net.http.slotsWire L))
          $$ [$Hca $Hsl $Hed $HwP $Hacc] as %nw0 %werr ⟨%w, %wres, HwP, Hsl, %Hw, #HE⟩
      ihave %Hwn := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
      cases werr
      · -- a write error
        try wp_auto
        wp_for_post
        close_tac
      have hres : wres = none := by
        rcases wres with _ | k
        · rfl
        · exact absurd rfl (net.netErr_ne_nil (Hwn.2 (by simp)))
      have hw : w = d.wire := Hw.2.2.1 hres
      subst hw
      iunfold writeP at HwP
      -- the answer at `i`
      ihave ⟨Hb, #Hlb⟩ := ownReader_hcLb br0 (net.connIface t) (hcErr γe) cn γ γe _ $$ Hb
      ihave #Hlaw := hcSt_law cn γ γe (net.http.respsWire (A.map RespSlot.ans)) A (L ++ [d.slot τ])
        rfl hAok (by rw [List.length_append, List.length_singleton]; omega) $$ [$Hlb $HlbL]
      try wp_auto
      wp_apply wp_ReadResponse br0 (net.connIface t) (hcSt cn γ γe) (hcErr γe)
          (net.http.respsWire (A.map RespSlot.ans)) (drvQ (L ++ [d.slot τ]) A.length) eof
          $$ [$Hhenv $Heof $Hstream $Hb $Hbound $Hlaw $Hfin] as %rp %rerr Hres
      icases Hres with (⟨%Hne, -⟩ | ⟨%Hnil, %rv, %st, %reason, %hc, %cl, %hm, %bi, %SB, %EB, Hrv,
        %Hrvf, Hhdr, HbiOk, HSB, %HSBb, #HEB, Hback⟩)
      · cases rerr with
        | nil => exact absurd rfl Hne
        | ok ei =>
          try wp_auto
          wp_for_post
          close_tac
      subst Hnil
      obtain ⟨rfl, rfl, Hbody⟩ := Hrvf
      try wp_auto
      try rw [Hbody]
      -- its body, to its end
      wp_apply wp_ReadAll bi SB EB [] eof HSBb $$ [$HbiOk $HSB $Heof]
        as %sl2 %rerr2 ⟨%ys, Hsl2, HSB, Hrd⟩
      try simp only [List.nil_append]
      icases Hrd with (⟨%Hn2, #HEys⟩ | ⟨%Hn2, -⟩)
      rotate_left
      · cases rerr2 with
        | nil => exact absurd rfl Hn2.1
        | ok e2 =>
          try wp_auto
          wp_for_post
          close_tac
      subst Hn2
      ihave HQ : (∃ ρ : Resp, ⌜ρ.st = rv.StatusCode' ∧ ρ.reason = reason ∧ ρ.hc = hc ∧
          ρ.close = cl ∧ (if cl then ys <+: ρ.body else ys = ρ.body)⌝ ∗
          □ drvQ (L ++ [d.slot τ]) A.length ρ : IProp GF) $$ []
      · iapply HEB $$ %ys %eof HEys
        ipureintro; rfl
      icases HQ with ⟨%ρ, %Hρ, #HQ⟩
      obtain ⟨Hρst, Hρre, Hρhc, Hρcl, Hρb⟩ := Hρ
      have hx : ρ.close = false → ys = ρ.body := by
        intro h
        rw [Hρcl] at h
        subst h
        simpa using Hρb
      ihave %Hchk := drvQ_chk L d τ ρ ys A.length (by omega) hx $$ [$Hτ $HQ]
      have hchk : chkPre d rv.StatusCode' hc ys := by
        rw [← Hρst, ← Hρhc]; exact Hchk.1
      -- `check`, `reached`
      ipersist Hrv
      ihave ⟨#Hsc, -⟩ := (net.http.Response.Response_access_load_StatusCode (GF := GF) rp rv
        DFrac.discard).access_strict $$ Hrv
      try wp_auto
      wp_apply wp_bytes_to_string sl2 ys (DFrac.own 1) $$ Hsl2 as Hsl2
      wp_apply wp_check qv d rp rv hc ys hq hchk $$ [$Hf $Hrv $Hhdr]
      try wp_auto
      wp_bind (App (Val #fr) (Val _))
      iapply wp_wand $$ (Hrf $$ %go!"keep-alive")
      iintro %v %Hv
      subst Hv
      try wp_auto
      wp_if_destruct
      · -- the `400`: the session ends
        wp_for_post
        close_tac
      · -- a handler's answer: the reader is past it
        have hne : ρ ≠ net.http.badResp := by
          intro h
          have h1 : ρ.st = net.http.badResp.st := congrArg Resp.st h
          exact Hif (Hρst.symm.trans h1)
        obtain ⟨hok, hcl, y, hy⟩ := Hchk.2 hne
        have hys : ys = ρ.body := hx hcl
        have hwire : net.http.respsWire ((A ++ [ρ]).map RespSlot.ans) =
            net.http.respsWire (A.map RespSlot.ans) ++
              net.http.respHeadWire rv.StatusCode' reason hc ++ ys := by
          rw [respsWire_snoc, List.append_assoc]
          unfold net.http.respWire
          rw [Hρst, Hρre, Hρhc, hys]
        ihave Hb : EtcdGrove.bufio.ownReader br0 (net.connIface t) (hcSt cn γ γe) (hcErr γe)
            (net.http.respsWire ((A ++ [ρ]).map RespSlot.ans)) $$ [Hback HSB]
        · rw [hwire]
          iapply Hback $$ %ys %eof HSB HEys
          ipureintro; rfl
        ihave Hsend : sendTok (Gg := hG.goose_globalGS) cn false
            (net.http.httpReqP (Gg := hG.goose_globalGS) drvP)
            (net.http.slotsWire (L ++ [d.slot τ])) $$ [HwP]
        · rw [slotsWire_snoc, slotWire_dslot]
          iexact HwP
        ihave #Hfs' : ([∗list] s ∈ L ++ [d.slot τ],
            net.http.slotFacts drvP s) $$ []
        · iapply BigSepL.bigSepL_snoc.2
          isplitl []
          · iexact Hfs
          iapply slotFacts_dslot d hd τ $$ Hτ
        have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := sess_succ i _ hi
        wp_for_post
        iframe
        iexists i + W64 1, A ++ [ρ], L ++ [d.slot τ]
        iframe
        isplitl []
        · iexact Hfs'
        ipureintro
        refine ⟨by rw [List.length_append, List.length_singleton, hA, hi1],
          by rw [List.length_append, List.length_singleton, hLl, hi1], ?_, ?_, by omega⟩
        · intro x hx'
          rcases List.mem_append.1 hx' with h | h
          · exact hAok x h
          · rw [List.mem_singleton] at h
            subst h
            exact ⟨hok, hcl⟩
        · intro s hs
          rcases List.mem_append.1 hs with h | h
          · exact hLok s h
          · rw [List.mem_singleton] at h
            subst h
            exact ⟨slotOk_dslot d hd τ, by simp [hy]⟩
    · -- the loop's end
      try wp_auto
      close_tac
  · ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
    obtain ⟨-, Hne⟩ := Hnet
    obtain ⟨pe, rfl⟩ := Hne (by simp)
    try wp_auto
    iapply HΦ
    itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
