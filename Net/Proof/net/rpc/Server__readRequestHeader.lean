/-
The proof of `Server.readRequestHeader` (`Net/Spec/net/rpc/Server__readRequestHeader.lean`): a
free `*Request` (`getRequest`), the codec's `ReadRequestHeader` through the reader's `recvTokL`
(`rd_acc_srv`). A failure (or an earlier one, `rerr`): `keepReading` stays `false` (the
comparisons with `io.EOF` and `io.ErrUnexpectedEOF` compare pointers; a new `errors.New` error
otherwise). A header: the request it is, taken (`req_hdr`: three later credits, the protocol
fact's and `req_hdr`'s two), its deposit and `srvServes`'s registration of its service; the loop
finds its last dot (`lastDotIdx_of`, `lastDotIdx_some`: the deposit's `splitSM`), the service is
found under `mapLock` (the registry's ghost map agrees), then the method in the service's map:
found, `methodTypeIs`; not, an `errors.New` error (`errNE`) and the deposit spent on `errOk`.
-/
module

public import Net.Spec.net.rpc.Server__readRequestHeader
public import Net.Spec.net.rpc.Server__getRequest
public import Net.Spec.net.rpc.serverCodec__ReadRequestHeader
public import Net.Proof.net.rpc.ServerGhost
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

set_option hygiene false in
/-- `readRequestHeader`'s end after a failed read: `keepReading` `false`, an error. -/
local macro "rrh_fin" : tactic =>
  `(tactic| (iapply HΦ; ileft; ipureintro; exact ⟨rfl, by simp [interface.mkOk]⟩))

set_option hygiene false in
/-- The new `errors.New` error of a failed read (`err.Error()` of the read's `rdErr`), then the
end. -/
local macro "rrh_new" : tactic =>
  `(tactic| (
    wp_bind (App (Val #(methods _ go!"Error" _)) (Val #()))
    iapply wp_rdErr_Error $$ Hre
    inext
    iintro %msg %-
    (try wp_auto)
    wp_apply wp_errors_New' as %x #HN
    rrh_fin))

set_option hygiene false in
/-- The comparisons with `io.EOF` (`x0`) and `io.ErrUnexpectedEOF` (`x1`) of a failed read's
pointer error `T`, `l`, then the end. -/
local macro "rrh_err" : tactic =>
  `(tactic| (
    (try simp only [interface.mkOk])
    by_cases hT : T = errors.errorString.ty
    · subst hT
      (try simp only [↓reduceIte])
      (try wp_auto)
      by_cases h0 : l = x0
      · rw [decide_eq_true h0]
        (try wp_auto)
        rrh_fin
      · rw [decide_eq_false h0]
        (try wp_auto)
        (try simp only [interface.mkOk, ↓reduceIte])
        (try wp_auto)
        by_cases h1 : l = x1
        · rw [decide_eq_true h1]
          (try wp_auto)
          rrh_fin
        · rw [decide_eq_false h1]
          (try wp_auto)
          rrh_new
    · have hT' : go.GoType.PointerType T ≠ go.GoType.PointerType errors.errorString.ty := by
        intro h; injection h with h; exact hT h
      simp only [hT', ↓reduceIte]
      (try wp_auto)
      simp only [interface.mkOk, hT', ↓reduceIte]
      (try wp_auto)
      rrh_new))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [sync.Assumptions] [net.Assumptions] [errors.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem Server.readRequestHeader.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_getRequest : Server.getRequest.spec (GF := GF) (hG := hG))
    (wp_ReadRequestHeader : serverCodec.ReadRequestHeader.spec (GF := GF) (hG := hG)) :
    Server.readRequestHeader.spec (GF := GF) (hG := hG) := by
  intro s γs C W a sc t cn la ra
  wp_start as ⟨#Hsrv, #Hserves, #Henv, #Hsc, Hrd⟩
  iunfold srvEnv at Henv
  icases Henv with ⟨#Hcli, -⟩
  ihave #Hcli' := Hcli
  iunfold cliEnv at Hcli'
  icases Hcli' with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  ihave #HefV' := HefV
  iunfold errors.newVar at HefV'
  icases HefV' with ⟨%xf, #Hef, -⟩
  iunfold srvCodecAt at Hsc
  icases Hsc with ⟨#Hrwc, #Hconn⟩
  ihave #HEOF := io.eof_of_init $$ Hio
  iunfold errors.newVar at HEOF
  icases HEOF with ⟨%x0, #Hx0, -⟩
  icombine Heof Hx0 gives %Heq0
  subst Heq0
  ihave #Hiu := io.isInit_access $$ Hio
  icases Hiu with ⟨-, -, -, -, -, #HU, -⟩
  iunfold errors.newVar at HU
  icases HU with ⟨%x1, #Hx1, -⟩
  icombine Hueof Hx1 gives %Heq1
  subst Heq1
  wp_auto
  wp_apply wp_getRequest s γs $$ Hsrv as %req Hreq
  iunfold rdrOwn at Hrd
  icases Hrd with ⟨%r0, Hrerr, Hst⟩
  icases Hst with (⟨%Hr0, %ps, %k, Hrs, %Hps⟩ | ⟨%Hr0, #Hre, %R, Hrecv⟩)
  · -- no read failed yet
    subst Hr0
    iunfold readerSt at Hrs
    icases Hrs with ⟨Hrecv, %Hb, Hrole⟩
    ihave HrL : recvTokL (Gg := hG.goose_globalGS) cn true (reqProto (Gg := hG.goose_globalGS) W a)
        (W.hs a ++ framesOf ps ++ []) $$ [Hrecv]
    · rw [List.append_nil]; iapply recvTok_L $$ Hrecv
    ihave #Hacc := rd_acc_srv W a cn (W.hs a ++ framesOf ps)
    wp_apply wp_ReadRequestHeader sc t cn true a la ra req _ interface.nil
        (fun got => recvTokL (Gg := hG.goose_globalGS) cn true
          (reqProto (Gg := hG.goose_globalGS) W a) (W.hs a ++ framesOf ps ++ got))
        _ _ ed _ $$ [$Hrwc $Hconn $Hio $Heof $Hueof $Hed $Hef $HefV $Hreq $HrL $Hrerr $Hacc]
      as %err (⟨⟨%Hc, -⟩, -⟩ | ⟨-, %got, HP, Hres⟩)
    · exact absurd rfl Hc
    icases Hres with (⟨%seq, %sm, ⟨%Hnil, %Hgot, %Hlen⟩, Hr, Hrerr⟩ |
      ⟨%Hne, Hr, #HE, %r1, Hrerr, %Hr1⟩)
    rotate_left
    · ihave #Hre := rdErr_read la ra _ _ ed _ true got err $$ [$HefV $Hef $Hio $Heof $Hueof $HE]
      ihave #Hre' := Hre
      iunfold rdErr at Hre'
      icases Hre' with ⟨-, %Hp⟩
      obtain ⟨T, l, rfl⟩ := Hp
      wp_auto
      rrh_err
    -- a header: request `k`, taken
    subst Hnil Hgot
    wp_auto_lc 3
    have hlen := Hlen
    unfold maxFrameN at hlen
    ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn true _ _ $$ HP
    iapply fupd_wp
    imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrT with HrT
    have hfr : W.hs a ++ framesOf ps ++ frameOf (reqHdr seq sm) =
        W.hs a ++ framesOf (ps ++ [reqHdr seq sm]) := by
      rw [framesOf_append, framesOf_cons, framesOf_nil, List.append_nil, List.append_assoc]
    rw [hfr]
    icases recvTok_proto (Gg := hG.goose_globalGS) cn true _ _ $$ HrT with ⟨HrT, #Hpp⟩
    imod req_hdr W a cn ps k (reqHdr seq sm) Hps Hb (by omega) $$ [$Hlc2 $Hlc3 $Hpp $Hrole]
      with ⟨%γ, %L, %r, #Hrpc, #Hlb, ⟨%Hr, %Hh, %Hk, %Hrok⟩, Hctr, Hdep, Hans⟩
    obtain ⟨hseq, hsm⟩ := reqHdr_inj (by rw [reqHdr_length] at hlen; omega) (by unfold reqOk at Hrok; omega) Hh
    subst hseq hsm
    imodintro
    iunfold reqDeposit at Hdep
    icases Hdep with ⟨%svc, %m, %S, %Φc, ⟨%Hsplit, %HSS⟩, #Hpost, HS⟩
    ihave #Hserves' := Hserves
    iunfold srvServes at Hserves'
    ihave #Hsv := Hserves' $$ %svc %S %HSS
    icases Hsv with ⟨#Hreg, #HerrOk⟩
    iunfold svcReg at Hreg
    icases Hreg with ⟨%sv, #Hel, #Hsvc⟩
    ihave Hpend : ansPend W a cn k r.sm Φc $$ [Hans]
    · iunfold ansPend
      iexists γ, L, r
      iframe Hrpc Hlb Hans Hpost
      ipureintro; exact ⟨Hr, rfl, Hk⟩
    ihave Hmid : rdrMid W a cn k r $$ [HrT Hctr]
    · iunfold rdrMid
      iexists γ, L, ps
      iframe HrT Hrpc Hlb Hctr
      ipureintro; exact ⟨Hr, Hps, Hb, Hrok⟩
    -- the loop's dot: request `k`'s last dot (the deposit's `splitSM`)
    obtain ⟨j, hj, hsvc, hm⟩ : ∃ j, lastDotIdx r.sm = some j ∧ r.sm.take j = svc ∧
        r.sm.drop (j + 1) = m := by
      unfold splitSM at Hsplit
      cases h : lastDotIdx r.sm with
      | none => rw [h] at Hsplit; cases Hsplit
      | some j =>
        rw [h] at Hsplit
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at Hsplit
        exact ⟨j, rfl, Hsplit.1, Hsplit.2⟩
    obtain ⟨hjl, hjd⟩ := lastDotIdx_some _ _ hj
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsml
    ihave HI : (∃ iv : w64, "i" ∷ i_ptr ↦ iv ∗ "dot" ∷ dot_ptr ↦ W64 (-1) ∗
        "%Hiv" ∷ ⌜-1 ≤ sint.Z iv ∧ sint.Z iv < r.sm.length ∧
          ∀ jj : Nat, sint.Z iv < jj → jj < r.sm.length → r.sm[jj]? ≠ some (W8 46)⌝ : IProp GF)
        $$ [i dot]
    · iexists _
      iframe i dot
      ipureintro
      refine ⟨by word, by word, fun jj h1 h2 => by exfalso; word⟩
    wp_for HI
    obtain ⟨Hiv1, Hiv2, Hiv3⟩ := Hiv
    by_cases hi0 : 0 ≤ sint.Z iv
    rotate_left
    · -- no dot at all: the deposit's last dot excludes it
      exfalso
      exact Hiv3 j (by omega) hjl hjd
    rw [decide_eq_true (by simpa using hi0)]
    simp only [↓reduceIte]
    wp_auto
    have hiv : sint.nat iv < r.sm.length := by
      have : sint.nat iv = (sint.Z iv).toNat := rfl
      omega
    obtain ⟨b, hb⟩ : ∃ b, r.sm[sint.nat iv]? = some b :=
      ⟨_, List.getElem?_eq_getElem hiv⟩
    rw [if_pos hi0, hb]
    wp_auto
    by_cases hb46 : b = W8 46
    rotate_left
    · -- not a dot: on to `i - 1`
      rw [decide_eq_false hb46]
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe i dot
      ipureintro
      refine ⟨by word, by word, fun jj h1 h2 => ?_⟩
      by_cases hjj : (jj : Int) = sint.Z iv
      · have : jj = sint.nat iv := by
          have : sint.nat iv = (sint.Z iv).toNat := rfl
          omega
        subst this; rw [hb]; intro h; exact hb46 (Option.some.inj h)
      · exact Hiv3 jj (by word) h2
    subst hb46
    rw [decide_eq_true rfl]
    wp_auto
    -- the last dot, at `iv`: the deposit's
    have hlast : lastDotIdx r.sm = some (sint.nat iv) := by
      refine lastDotIdx_of r.sm (sint.nat iv) hiv hb (fun jj h1 h2 => Hiv3 jj ?_ h2)
      have : sint.nat iv = (sint.Z iv).toNat := rfl
      omega
    rw [hj] at hlast
    have hjiv : j = sint.nat iv := Option.some.inj hlast
    subst hjiv
    wp_for_post
    rw [decide_eq_false (by simp; omega)]
    (try simp only [↓reduceIte])
    wp_auto
    have hz : sint.Z (W64 0) = 0 := by decide
    have hivn : (sint.nat iv : Int) = sint.Z iv := by
      have : sint.nat iv = (sint.Z iv).toNat := rfl
      omega
    rw [if_pos (by rw [hz]; omega)]
    simp only [List.drop_zero, Nat.sub_zero, hsvc]
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
    have hlenz : sint.Z (W64 (r.sm.length : Int)) = r.sm.length := by word
    rw [if_pos (by rw [hiv1, hlenz]; omega)]
    have hiv1n : sint.nat (iv + W64 1) = sint.nat iv + 1 := by
      have h1 : sint.nat (iv + W64 1) = (sint.Z (iv + W64 1)).toNat := rfl
      omega
    have hlenn : sint.nat (W64 (r.sm.length : Int)) = r.sm.length := by
      have h1 : sint.nat (W64 (r.sm.length : Int)) = (sint.Z (W64 (r.sm.length : Int))).toNat := rfl
      omega
    rw [hiv1n, hlenn, List.take_of_length_le (by simp), hm]
    wp_auto
    ihave #Hs2 := Hsrv
    iunfold isServer at Hs2
    icases Hs2 with ⟨-, #Hmu, -, -⟩
    wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown, Hinv⟩
    iunfold svcMapInv at Hinv
    icases Hinv with ⟨%smp, %M3, Hsm, HM3, Hγ⟩
    wp_auto
    wp_apply (wp_map_lookup2 go.string (go.GoType.PointerType net.rpc.service.ty) smp M3 svc
      (DFrac.own 1)) $$ HM3 as HM3
    ihave %Hlk := ghost_map_lookup $$ Hγ Hel
    rw [show M3 !! svc = some sv from Hlk]
    simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
    wp_apply wp_Unlock _ (svcMapInv γs s) $$ [$Hsync $Hmu $Hown Hsm HM3 Hγ]
    · iunfold svcMapInv
      iexists smp, _
      iframe Hsm HM3 Hγ
    iunfold svcIs at Hsvc
    icases Hsvc with ⟨%rcvr, %mp, %MT, #Hrcvr, #Hmeth, #Hmp, #HMT⟩
    wp_auto
    wp_apply (wp_map_lookup1 go.string (go.GoType.PointerType net.rpc.methodType.ty) mp MT m
      DFrac.discard) $$ Hmp as -
    ihave #HerrOk' := HerrOk
    iunfold errOk at HerrOk'
    obtain ⟨mt, hmt⟩ : ∃ mt : Loc, (MT !! m).getD (_root_.Perennial.zero_val Loc) = mt := ⟨_, rfl⟩
    rw [hmt]
    by_cases hnull : mt = null
    · -- not registered: an error, and the deposit spent on the error answers
      subst hnull
      wp_auto
      wp_apply wp_errors_New' as %x #HN
      iapply HΦ
      iright
      isplitr
      · ipureintro; rfl
      iexists k, r, Φc
      iframe Hr Hrerr Hmid Hpend
      iright
      isplitr
      · ipureintro; simp [interface.mkOk]
      isplitr
      · iapply errNE_errorString x _ (by simp) $$ HN
      iunfold errCont
      iintro %msg %hmsg
      iapply HerrOk' $$ %m %r.body %Φc %msg %hmsg HS
    · have hsome : MT !! m = some mt := by
        cases hl : MT !! m with
        | none => rw [hl] at hmt; exact absurd hmt.symm hnull
        | some v => rw [hl] at hmt; rw [← hmt]; rfl
      ihave #Hmt := BigSepM.bigSepM_lookup
        (Φ := fun m mt => methodTypeIs (GF := GF) C rcvr (S m) mt) (by rw [gmap_get?_eq]; exact hsome)
        $$ HMT
      rw [decide_eq_false hnull]
      wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; rfl
      iexists k, r, Φc
      iframe Hr Hrerr Hmid Hpend
      ileft
      isplitr
      · ipureintro; rfl
      iexists S, m, rcvr
      iframe HS HerrOk Hrcvr Hmt
  · -- a read failed: `rerr` holds its error
    ihave HrL : recvTokL (Gg := hG.goose_globalGS) cn true (reqProto (Gg := hG.goose_globalGS) W a)
        (R ++ []) $$ [Hrecv]
    · rw [List.append_nil]; iapply recvTok_L $$ Hrecv
    ihave #Hacc := rd_acc_srv W a cn R
    wp_apply wp_ReadRequestHeader sc t cn true a la ra req _ r0
        (fun got => recvTokL (Gg := hG.goose_globalGS) cn true
          (reqProto (Gg := hG.goose_globalGS) W a) (R ++ got))
        _ _ ed _ $$ [$Hrwc $Hconn $Hio $Heof $Hueof $Hed $Hef $HefV $Hreq $HrL $Hrerr $Hacc]
      as %err (⟨⟨-, %He⟩, -⟩ | ⟨%Hc, -⟩)
    · subst He
      ihave #Hre' := Hre
      iunfold rdErr at Hre'
      icases Hre' with ⟨-, %Hp⟩
      obtain ⟨T, l, rfl⟩ := Hp
      wp_auto
      rrh_err
    · exact absurd Hc Hr0

end proof

end net.rpc
end Perennial
