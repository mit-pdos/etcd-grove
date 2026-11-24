/-
The proof of `Client.send` (`Net/Spec/net/rpc/Client__send.lean`). Under `reqMutex` (`sendInv`) and
`mutex` (`muInv`): refused (shut down or closing), the call fails with `ErrShutdown` (`Call.done`),
ticket `none`; else it is numbered `n` (a time receipt for the number, `n + 1 < 2 ^ 64`), its names
allocated and recorded (`nm`), its entry put in `pending` (`callRes`), ticket `some n`. Then
`WriteRequest`: without a write error before, the encoding's continuation appends the request
(`req_append`); after a failed write the call, if still pending, fails with the write's error.
-/
module

public import Net.Spec.net.rpc.Client__send
public import Net.Spec.net.rpc.Call__done
public import Net.Spec.net.rpc.clientCodec__WriteRequest
public import Net.Proof.net.rpc.ClientGhost
public import Net.Proof.net.rpc.Errs
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS] [sync.Assumptions] [net.Assumptions]

theorem uint_nat_W64_lt (n : Nat) (h : n < 2 ^ 64) : uint.nat (W64 n) = n := by
  word

theorem nm_fresh {X : Type} (NM : GMap Nat X) (n : Nat)
    (h : ∀ i, (NM.lookup i).isSome → i < n) : NM.lookup n = none := by
  cases hl : NM.lookup n with
  | none => rfl
  | some v =>
    exfalso
    have := h n (by rw [hl]; rfl)
    exact Nat.lt_irrefl _ this

theorem nm_insert_bound {X : Type} (NM : GMap Nat X) (n : Nat) (x : X)
    (h : ∀ i, (NM.lookup i).isSome → i < n) :
    ∀ i, ((NM.insert n x).lookup i).isSome → i < n + 1 := by
  intro i hi
  by_cases hin : i = n
  · omega
  · have hne : n ≠ i := Ne.symm hin
    have := h i (by simpa [hne] using hi)
    omega

theorem Client.send.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_WriteRequest : clientCodec.WriteRequest.spec (GF := GF) (hG := hG))
    (wp_done : Call.done.spec (GF := GF) (hG := hG)) :
    Client.send.spec (GF := GF) (hG := hG) := by
  intro c W a γ pc sm svc M S args reply ch γt γf K Φm Rargs D Θ C
  wp_start as ⟨#Hcl, %Hsv, #Hset, Henc, HD, #Hdec, Hγt, #Hf, Herr, Hdone⟩
  unfold isClientN clientAt
  icases Hcl with ⟨%cc, %t, %cn, %la, %ra, #Hcodec, #Hrwc, #Hconn, #Hci, #Hrpc, #Hsl, #Henv,
    #Hsmu, #Hmu⟩
  ihave #Henv' := Henv
  unfold cliEnv
  icases Henv' with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply +noauto wp_Lock _ _ $$ [$Hsync $Hsmu] as ⟨Hsown, Hsinv⟩
  wp_take_receipt as Hr1
  wp_auto
  iunfold sendInv at Hsinv
  icases Hsinv with ⟨%rq, %w0, %L, %Wd, %n1, Hreq, Hwerr, Hsend, Hreqs, Hsq1, ⟨%sd1, Hd1⟩,
    #Hw0e, ⟨%HLok, %HLn, %HWd, %Hw0⟩⟩
  wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown, Hinv⟩
  iunfold muInv at Hinv
  icases Hinv with ⟨%sq, %n, %mp, %m, %sd, %cls, %NM, Hseq, Hpend, Hmp, Hsd, Hcls, Hsq, Hr,
    ⟨%Hsqn, %Hbound⟩, Hdown, Hnm, %HNM, Hrest⟩
  ihave %Hsqa := ghostVar_agree $$ Hsq1 Hsq
  obtain ⟨-, rfl⟩ := Hsqa
  ihave #HesV' := HesV
  iunfold errors.newVar at HesV'
  icases HesV' with ⟨%xs, #Hxs, -⟩
  cases sd <;> cases cls
  rotate_left
  iterate 3 (
    -- refused: `ErrShutdown`
    wp_auto
    wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
        Hrest]
    · iunfold muInv
      iexists sq, n1, mp, m, _, _, NM
      iframe Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm Hrest
      ipureintro; exact ⟨⟨Hsqn, Hbound⟩, HNM⟩
    imod ghost_map_insert_persist () (none : Option Nat) (by rfl) $$ Hγt with ⟨-, #Htk0⟩
    ihave #Htk : ticket γt none $$ []
    · iunfold ticket; iexact Htk0
    wp_apply wp_done pc sm args reply ch γ.conn γt γf K Φm Θ D none
        (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xs)
        $$ [$Hdbg $Hf $Htk $Hdone $Herr HD]
    · iunfold callPost
      iright; iright
      isplitr
      · ipureintro; exact ⟨by simp [interface.mkOk], notServerErr_errorString xs⟩
      isplitr
      · iapply errAny_newVar $$ HesV Hxs
      ileft; iexact HD
    wp_apply wp_Unlock _ (sendInv γ c cc cn W a) $$ [$Hsync $Hsmu $Hsown Hreq Hwerr Hsend Hreqs Hsq1
        Hd1]
    · iunfold sendInv
      iexists rq, w0, L, Wd, n1
      iframe Hreq Hwerr Hsend Hreqs Hsq1
      isplitl [Hd1]
      · iexists sd1; iexact Hd1
      iframe Hw0e
      ipureintro; exact ⟨HLok, HLn, HWd, Hw0⟩
    iapply HΦ
    iexists none
    iframe Htk
    iunfold sendRes
    iright
    iframe Henc
    unfold unsent
    itrivial)
  -- numbered `n1`
  wp_auto_lc 2
  subst Hsqn
  icases receipt_add_one_lt n1 $$ [$Hr1 $Hr] with ⟨%Hn1, Hr⟩
  have hn1 : n1 + 1 < 2 ^ 64 := Nat.lt_of_lt_of_le Hn1 Hbound
  have hu : uint.nat (W64 n1) = n1 := uint_nat_W64_lt n1 (by omega)
  wp_apply (wp_mapInsert (K := w64) (V := Loc) go.uint64 mp m (W64 n1) pc) $$ Hmp as Hmp
  imod saved_pred_alloc (GF := GF) (fun p : List w8 × GoString => Φm p.1 p.2) DFrac.discard
    trivial with ⟨%post, #Hpost⟩
  imod token_alloc (GF := GF) with ⟨%col, Hcol⟩
  imod token_alloc (GF := GF) with ⟨%ap, Hap⟩
  have hNM : NM.lookup n1 = none := nm_fresh NM n1 HNM
  imod ghost_map_insert_persist n1 ((post, col, ap) : GName × GName × GName) hNM $$ Hnm
    with ⟨Hnm, #Hnmn⟩
  imod ghost_map_insert_persist () (some n1 : Option Nat) (by rfl) $$ Hγt with ⟨-, #Htk0⟩
  ihave #Htk : ticket γt (some n1) $$ []
  · iunfold ticket; iexact Htk0
  ihave %Hda := ghostVar_agree $$ Hd1 Hdown
  obtain ⟨-, rfl⟩ := Hda
  imod ghostVar_update_halves (n1 + 1) γ.sq n1 n1 $$ Hsq1 Hsq with ⟨Hsq1, Hsq⟩
  wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
      Hrest Herr Hdone HD Hcol]
  · iunfold muInv
    iexists W64 n1 + W64 1, n1 + 1, mp, _, false, false, _
    iframe Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
    isplitr
    · ipureintro; exact ⟨by word, Hbound⟩
    isplitr
    · ipureintro; exact nm_insert_bound NM n1 _ HNM
    simp only [Bool.false_eq_true, ite_false]
    iapply BigSepM.bigSepM_insert_elim $$ [Herr Hdone HD Hcol] Hrest
    iunfold callRes
    iexists sm, args, reply, ch, γt, γf, K, Φm, Θ, D, C, post, col, ap
    rw [hu]
    iframe Hf Herr Htk Hdone Hpost Hcol Hnmn HD
    isplitr
    · rcases reply with e | _
      · simp only [bodyDecG]
        iframe Hset
        iexact Hdec
      · exact absurd rfl Hsv.2.2.1
    ipureintro; exact Hsv.2.2
  ihave #Hf' := Hf
  iunfold callFields at Hf'
  icases Hf' with ⟨#Hfsm, #Hfargs, #Hfrep, #Hfch⟩
  wp_auto
  cases w0 with
  | ok e =>
    ihave Hupd : (⌜interface.ok e = interface.nil⌝ -∗ reqUpd (hG := hG) cn
        (reqProto (Gg := hG.goose_globalGS) W a) Wd (W64 n1) sm
        (fun bs => iprop(S M bs Φm ∗ Rargs)) (fun _ => iprop(True))) $$ []
    · iintro %h; cases h
    wp_apply wp_WriteRequest cc t cn false a la ra (structFieldRef net.rpc.Client go!"request" c) _
        args (interface.ok e) ed C (reqProto (Gg := hG.goose_globalGS) W a) Wd
        (fun bs => iprop(S M bs Φm ∗ Rargs)) (fun _ => iprop(True))
        $$ [$Hrwc $Hconn $Hed $Hwerr $Hreq $Hset $Hsend $Henc $Hupd] as %err ⟨Hreq, Hres⟩
    icases Hres with (⟨%Herr, Hwerr, Hsend, Henc⟩ | ⟨%Hn, -⟩)
    rotate_left
    · cases Hn
    subst Herr
    icases Hw0e with (%Hx | ⟨%Hns, #Hea⟩)
    · cases Hx
    wp_auto
    wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown2, Hinv2⟩
    iunfold muInv at Hinv2
    icases Hinv2 with ⟨%sq2, %n2, %mp2, %m2, %sd2, %cls2, %NM2, Hseq2, Hpend2, Hmp2, Hsd2, Hcls2,
      Hsq2, Hr2, %Hb2, Hdown2, Hnm2, %HNM2, Hrest2⟩
    ihave %Hda2 := ghostVar_agree $$ Hd1 Hdown2
    obtain ⟨-, rfl⟩ := Hda2
    simp only [Bool.false_eq_true, ite_false]
    wp_auto
    wp_apply (wp_map_lookup1 (K := w64) (V := Loc) go.uint64
      (go.GoType.PointerType net.rpc.Call.ty) mp2 m2 (W64 n1) (DFrac.own 1)) $$ Hmp2 as Hmp2
    wp_apply (wp_mapDelete (K := w64) (V := Loc) mp2 m2 (W64 n1) go.uint64
      (go.GoType.PointerType net.rpc.Call.ty)) $$ Hmp2 as Hmp2
    cases hlk : m2.lookup (W64 n1) with
    | none =>
      rw [GMap.delete_notin _ _ hlk]
      wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown2 Hseq2 Hpend2 Hmp2 Hsd2 Hcls2 Hsq2 Hr2
          Hdown2 Hnm2 Hrest2]
      · iunfold muInv
        iexists sq2, n2, mp2, m2, false, cls2, NM2
        iframe Hseq2 Hpend2 Hmp2 Hsd2 Hcls2 Hsq2 Hr2 Hdown2 Hnm2
        isplitr
        · ipureintro; exact Hb2
        isplitr
        · ipureintro; exact HNM2
        simp only [Bool.false_eq_true, ite_false]
        iexact Hrest2
      wp_apply wp_Unlock _ (sendInv γ c cc cn W a) $$ [$Hsync $Hsmu $Hsown Hreq Hwerr Hsend Hreqs Hsq1
          Hd1]
      · iunfold sendInv
        iexists _, interface.ok e, L, Wd, n1 + 1
        iframe Hreq Hwerr Hsend Hreqs Hsq1
        isplitl [Hd1]
        · iexists false; iexact Hd1
        isplitr
        · iright; iframe Hea; ipureintro; exact Hns
        ipureintro; exact ⟨HLok, by omega, HWd, fun h => by cases h⟩
      iapply HΦ
      iexists some n1
      iframe Htk
      iunfold sendRes
      iright
      iframe Henc
      unfold unsent
      iexists post, col, ap
      iframe Hnmn Hap
    | some pc' =>
      icases (BigSepM.bigSepM_delete (Φ := fun s pc => callRes (hG := hG) γ.conn s pc)
        (by rw [gmap_get?_eq]; exact hlk)).1 $$ Hrest2 with ⟨Hcr, Hrest2⟩
      wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown2 Hseq2 Hpend2 Hmp2 Hsd2 Hcls2 Hsq2 Hr2
          Hdown2 Hnm2 Hrest2]
      · iunfold muInv
        iexists sq2, n2, mp2, _, false, cls2, NM2
        iframe Hseq2 Hpend2 Hmp2 Hsd2 Hcls2 Hsq2 Hr2 Hdown2 Hnm2
        isplitr
        · ipureintro; exact Hb2
        isplitr
        · ipureintro; exact HNM2
        simp only [Bool.false_eq_true, ite_false]
        iexact Hrest2
      iunfold callRes at Hcr
      icases Hcr with ⟨%sm', %args', %reply', %ch', %γt', %γf', %K', %Φ', %Θ', %D', %C', %post',
        %col', %ap', #Hf2, Herr2, #Htk2, Hdone2, -, -, -, HD2, -, ⟨%Hrep', %Hpc'⟩⟩
      rw [decide_eq_false Hpc']
      simp only [Option.getD_some]
      wp_auto
      wp_apply wp_done pc' sm' args' reply' ch' γ.conn γt' γf' K' Φ' Θ' D' _ (interface.ok e)
          $$ [$Hdbg $Hf2 $Htk2 $Hdone2 $Herr2 HD2]
      · iunfold callPost
        iright; iright
        isplitr
        · ipureintro; exact ⟨(by simp), Hns⟩
        isplitr
        · iexact Hea
        ileft; iexact HD2
      wp_apply wp_Unlock _ (sendInv γ c cc cn W a) $$ [$Hsync $Hsmu $Hsown Hreq Hwerr Hsend Hreqs Hsq1
          Hd1]
      · iunfold sendInv
        iexists _, interface.ok e, L, Wd, n1 + 1
        iframe Hreq Hwerr Hsend Hreqs Hsq1
        isplitl [Hd1]
        · iexists false; iexact Hd1
        isplitr
        · iright; iframe Hea; ipureintro; exact Hns
        ipureintro; exact ⟨HLok, by omega, HWd, fun h => by cases h⟩
      iapply HΦ
      iexists some n1
      iframe Htk
      iunfold sendRes
      iright
      iframe Henc
      unfold unsent
      iexists post, col, ap
      iframe Hnmn Hap
  | nil =>
    obtain ⟨hWd, hLn⟩ := Hw0 rfl
    subst hWd
    ihave Hupd : (⌜(interface.nil : GoInterface) = interface.nil⌝ -∗ reqUpd (hG := hG) cn
        (reqProto (Gg := hG.goose_globalGS) W a) (W.hs a ++ reqsWire L) (W64 n1) sm
        (fun bs => iprop(S M bs Φm ∗ Rargs))
        (fun eb => iprop(Rargs ∗ monoListAuthOwn γ.conn.reqs (1 : Qp).half (L ++ [(sm, eb, post, col)]) ∗
          ⌜reqOk (sm, eb, post, col)⌝))) $$ [Hreqs Hlc1 Hap]
    · iintro -
      iunfold reqUpd
      iintro %eb %hfit ⟨HS, HR⟩
      ihave Hr : (|={⊤}=> monoListAuthOwn γ.conn.reqs (1 : Qp).half (L ++ [(sm, eb, post, col)]) ∗
          □ reqProto (Gg := hG.goose_globalGS) W a cn
            (W.hs a ++ reqsWire L ++ reqWire (W64 n1) sm eb) : IProp GF) $$ [Hreqs Hlc1 Hap HS]
      · iapply req_append W a cn γ.conn L n1 hLn sm svc M S eb Φm post col ap HLok (by omega) hfit.1
          hfit.2 ⟨Hsv.1, Hsv.2.1⟩ $$ [$Hrpc $Hsl $Hlc1 $Hreqs $Hnmn $Hap $Hpost $HS]
      imod Hr with ⟨Hh, #Hp⟩
      imodintro
      simp only []
      iframe Hp HR Hh
      ipureintro; exact hfit
    wp_apply wp_WriteRequest cc t cn false a la ra (structFieldRef net.rpc.Client go!"request" c) _
        args interface.nil ed C (reqProto (Gg := hG.goose_globalGS) W a) (W.hs a ++ reqsWire L)
        (fun bs => iprop(S M bs Φm ∗ Rargs))
        (fun eb => iprop(Rargs ∗ monoListAuthOwn γ.conn.reqs (1 : Qp).half (L ++ [(sm, eb, post, col)]) ∗
          ⌜reqOk (sm, eb, post, col)⌝))
        $$ [$Hrwc $Hconn $Hed $Hwerr $Hreq $Hset $Hsend $Henc $Hupd] as %err ⟨Hreq, Hres⟩
    icases Hres with (⟨%Hne, -⟩ | ⟨-, %eb, ⟨HR, Hh, %Hrok⟩, Hout⟩)
    · exact Hne.elim
    icases Hout with (⟨%Herr, Hwerr, Hsend⟩ | ⟨%w, %k, ⟨%Hw, %Hwne⟩, Hwerr, Hsend, #HE⟩)
    · subst Herr
      wp_auto
      wp_apply wp_Unlock _ (sendInv γ c cc cn W a) $$ [$Hsync $Hsmu $Hsown Hreq Hwerr Hsend Hh Hsq1
          Hd1]
      · iunfold sendInv
        iexists _, _, L ++ [(sm, eb, post, col)], _, n1 + 1
        iframe Hreq Hwerr Hsend Hh Hsq1
        isplitl [Hd1]
        · iexists false; iexact Hd1
        isplitr
        · ileft; ipureintro; rfl
        ipureintro
        refine ⟨fun r hr => ?_, by simp; omega, ?_, fun _ => ⟨?_, by simp; omega⟩⟩
        · rcases List.mem_append.1 hr with hr | hr
          · exact HLok r hr
          · simp at hr; subst hr; exact Hrok
        · rw [reqsWire_append, hLn, List.append_assoc]; exact List.prefix_refl _
        · rw [reqsWire_append, hLn, List.append_assoc]
      iapply HΦ
      iexists some n1
      iframe Htk
      iunfold sendRes
      ileft
      iexact HR
    · ihave #HEa := errAny_resErr $$ HE
      ihave %HEns := notServerErr_resErr $$ HE
      ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
      obtain ⟨-, Hne⟩ := Hnet
      obtain ⟨pe, rfl⟩ := Hne (by simp)
      wp_auto
      wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown2, Hinv2⟩
      iunfold muInv at Hinv2
      icases Hinv2 with ⟨%sq2, %n2, %mp2, %m2, %sd2, %cls2, %NM2, Hseq2, Hpend2, Hmp2, Hsd2, Hcls2,
        Hsq2, Hr2, %Hb2, Hdown2, Hnm2, %HNM2, Hrest2⟩
      ihave %Hda2 := ghostVar_agree $$ Hd1 Hdown2
      obtain ⟨-, rfl⟩ := Hda2
      simp only [Bool.false_eq_true, ite_false]
      wp_auto
      wp_apply (wp_map_lookup1 (K := w64) (V := Loc) go.uint64
        (go.GoType.PointerType net.rpc.Call.ty) mp2 m2 (W64 n1) (DFrac.own 1)) $$ Hmp2 as Hmp2
      wp_apply (wp_mapDelete (K := w64) (V := Loc) mp2 m2 (W64 n1) go.uint64
        (go.GoType.PointerType net.rpc.Call.ty)) $$ Hmp2 as Hmp2
      cases hlk : m2.lookup (W64 n1) with
      | none =>
        rw [GMap.delete_notin _ _ hlk]
        wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown2 Hseq2 Hpend2 Hmp2 Hsd2 Hcls2 Hsq2 Hr2
            Hdown2 Hnm2 Hrest2]
        · iunfold muInv
          iexists sq2, n2, mp2, m2, false, cls2, NM2
          iframe Hseq2 Hpend2 Hmp2 Hsd2 Hcls2 Hsq2 Hr2 Hdown2 Hnm2
          isplitr
          · ipureintro; exact Hb2
          isplitr
          · ipureintro; exact HNM2
          simp only [Bool.false_eq_true, ite_false]
          iexact Hrest2
        wp_apply wp_Unlock _ (sendInv γ c cc cn W a) $$ [$Hsync $Hsmu $Hsown Hreq Hwerr Hsend Hh Hsq1
            Hd1]
        · iunfold sendInv
          iexists _, _, L ++ [(sm, eb, post, col)], _, n1 + 1
          iframe Hreq Hwerr Hsend Hh Hsq1
          isplitl [Hd1]
          · iexists false; iexact Hd1
          isplitr
          · iright; iframe HEa; ipureintro; exact HEns
          ipureintro
          refine ⟨fun r hr => ?_, by simp; omega, ?_, fun h => ?_⟩
          · rcases List.mem_append.1 hr with hr | hr
            · exact HLok r hr
            · simp at hr; subst hr; exact Hrok
          · rw [reqsWire_append, hLn, List.append_assoc]
            exact (List.prefix_append_right_inj _).2 ((List.prefix_append_right_inj _).2 Hw)
          · exact absurd h (by simp [interface.mkOk])
        iapply HΦ
        iexists some n1
        iframe Htk
        iunfold sendRes
        ileft
        iexact HR
      | some pc' =>
        icases (BigSepM.bigSepM_delete (Φ := fun s pc => callRes (hG := hG) γ.conn s pc)
          (by rw [gmap_get?_eq]; exact hlk)).1 $$ Hrest2 with ⟨Hcr, Hrest2⟩
        wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown2 Hseq2 Hpend2 Hmp2 Hsd2 Hcls2 Hsq2 Hr2
            Hdown2 Hnm2 Hrest2]
        · iunfold muInv
          iexists sq2, n2, mp2, _, false, cls2, NM2
          iframe Hseq2 Hpend2 Hmp2 Hsd2 Hcls2 Hsq2 Hr2 Hdown2 Hnm2
          isplitr
          · ipureintro; exact Hb2
          isplitr
          · ipureintro; exact HNM2
          simp only [Bool.false_eq_true, ite_false]
          iexact Hrest2
        iunfold callRes at Hcr
        icases Hcr with ⟨%sm', %args', %reply', %ch', %γt', %γf', %K', %Φ', %Θ', %D', %C', %post',
          %col', %ap', #Hf2, Herr2, #Htk2, Hdone2, -, -, -, HD2, -, ⟨%Hrep', %Hpc'⟩⟩
        rw [decide_eq_false Hpc']
        simp only [Option.getD_some]
        wp_auto
        wp_apply wp_done pc' sm' args' reply' ch' γ.conn γt' γf' K' Φ' Θ' D' _ (interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe)
            $$ [$Hdbg $Hf2 $Htk2 $Hdone2 $Herr2 HD2]
        · iunfold callPost
          iright; iright
          isplitr
          · ipureintro; exact ⟨(by simp [interface.mkOk]), HEns⟩
          isplitr
          · iexact HEa
          ileft; iexact HD2
        wp_apply wp_Unlock _ (sendInv γ c cc cn W a) $$ [$Hsync $Hsmu $Hsown Hreq Hwerr Hsend Hh Hsq1
            Hd1]
        · iunfold sendInv
          iexists _, _, L ++ [(sm, eb, post, col)], _, n1 + 1
          iframe Hreq Hwerr Hsend Hh Hsq1
          isplitl [Hd1]
          · iexists false; iexact Hd1
          isplitr
          · iright; iframe HEa; ipureintro; exact HEns
          ipureintro
          refine ⟨fun r hr => ?_, by simp; omega, ?_, fun h => ?_⟩
          · rcases List.mem_append.1 hr with hr | hr
            · exact HLok r hr
            · simp at hr; subst hr; exact Hrok
          · rw [reqsWire_append, hLn, List.append_assoc]
            exact (List.prefix_append_right_inj _).2 ((List.prefix_append_right_inj _).2 Hw)
          · exact absurd h (by simp [interface.mkOk])
        iapply HΦ
        iexists some n1
        iframe Htk
        iunfold sendRes
        ileft
        iexact HR


end proof

end net.rpc
end Perennial
