/-
The proof of `connReader.Read` (`Net/Spec/net/http/connReader__Read.lean`) in the head phase: under
the mutex the phase is the main one (the main thread's half of `γ.ph`), so the main thread owns the
fields; at the read limit `io.EOF`, an empty `p` at once, else `p` cut at the limit, `inRead` set and
the mutex released; the connection's `Read` (`net.Conn.Read.spec` with the library's `read_au`) into
`p`: with `read_dead_au` (the end's read deadline not set: no timeout; an error makes the reading
dead, `readDead`, recorded in the once-cell `γe`), or, once dead, `read_after_dead_au` (nothing
delivered); then under the mutex `inRead` cleared, on an error the connection's context canceled
(`handleReadErrorLocked`), the limit lowered, and the condition variable broadcast.
-/
module

public import Net.Spec.net.http.connReader__Read
public import Net.Spec.net.Conn__Read
public import Net.Proof.net.http.ConnReaderLemmas
public import Proof.bufio.Base
public import GooseLang.Ext.Net.Proto
public import Net.Proof.net.Errors

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS] [net.Assumptions] [field_sem : net.FieldAssumptions]

theorem drop_take_append (xs : List w8) (m k : Nat) (hm : m ≤ k) :
    (xs.take k).drop m ++ xs.drop k = xs.drop m := by
  rw [List.drop_take]
  have : xs.drop k = (xs.drop m).drop (k - m) := by rw [List.drop_drop]; congr 1; omega
  rw [this, List.take_append_drop]

/-- A slice cut at `k` (`p[:k]`), and the whole slice back with what the cut one then holds. -/
theorem slice_cut (p : GoSlice) (xs : List w8) (k : w64)
    (hk : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z p.len) :
    (p ↦* xs : IProp GF) ⊢ slice.slice p w8 (W64 0) k ↦* xs.take (sint.nat k) ∗
      (∀ ys : List w8, ⌜ys.length ≤ sint.nat k⌝ -∗
        slice.slice p w8 (W64 0) k ↦* (ys ++ (xs.take (sint.nat k)).drop ys.length) -∗
        p ↦* (ys ++ xs.drop ys.length)) := by
  iintro Hp
  ihave %Hlen := ownSlice_len $$ Hp
  icases (ownSlice_split_all k p (DFrac.own 1) xs hk).1 $$ Hp with ⟨H1, H2⟩
  iframe H1
  iintro %ys %hys H1
  have hxk : sint.nat k ≤ xs.length := by rw [Hlen.1]; exact Int.toNat_le_toNat hk.2
  have h00 : sint.nat (W64 0) = 0 := rfl
  have h0 : sint.Z (W64 0) = 0 := rfl
  iapply ownSlice_trivial_slice_2
  ihave H := ownSlice_combine k p (DFrac.own 1) _ (xs.drop (sint.nat k)) (W64 0) p.len
    ⟨by simp only [List.length_append, List.length_drop, List.length_take, h00]; omega,
      by rw [h0]; omega, by rw [h0]; omega, hk.2⟩ $$ H1 H2
  rw [List.append_assoc, drop_take_append xs _ _ hys]
  iexact H

/-- A read error of the connection is a pointer (`io.ptrTyped`): `io.EOF`'s `*errorString`, or an
`*OpError`. -/
theorem readErr_ptrTyped (r : ReadRes) (la ra ed err : GoInterface) (xe : Loc) :
    net.ReadErr (GF := GF) r (interface.mkOk errors.errorString.ty.PointerType #xe) la ra ed err ⊢
      ⌜_root_.Perennial.io.ptrTyped err ∧ (r.got = [] ∨ err = interface.nil)⌝ := by
  cases r with
  | bytes bs =>
    simp only [net.ReadErr]
    iintro %h; subst h; ipureintro; exact ⟨_root_.Perennial.io.ptrTyped_nil, Or.inr rfl⟩
  | eof =>
    simp only [net.ReadErr]
    iintro %h; subst h; ipureintro
    refine ⟨?_, Or.inl rfl⟩
    intro ii T h hT
    simp only [interface.mkOk] at h
    cases h; exact ⟨xe, rfl⟩
  | err k =>
    simp only [net.ReadErr]
    iintro HE
    ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
    obtain ⟨-, Hne⟩ := Hnet
    obtain ⟨pe, rfl⟩ := Hne (by simp)
    ipureintro
    refine ⟨?_, Or.inl rfl⟩
    intro ii T h hT
    simp only [interface.mkOk] at h
    cases h; exact ⟨pe, rfl⟩

/-- `"read" ++ …` is not `"message too large"`. -/
theorem opErrMsg_read_ne (m : GoString) (h : net.opErrMsg go!"read" m) : m ≠ go!"message too large" := by
  obtain ⟨s1, s2, rfl⟩ := h
  intro h
  have := congrArg List.head? h
  simp at this

/-- A read error of the connection is `io.EOF`'s `*errorString` or an `*OpError` of a read
(`crErrId`), whose `Error()` returns a string other than `"message too large"` (`errMsgOk`): `"EOF"`
(`errors.newVar`), or `net.wp_OpError_Error`'s `"read …"`. -/
theorem readErr_msgOk (r : ReadRes) (la ra ed err : GoInterface) (xe : Loc) (msg : GoString)
    (hmsg : msg ≠ go!"message too large") :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
        WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #xe))
          (Val #())) {{ Φ }}) ∗
      globalAddr io.EOF ↦□ interface.mkOk errors.errorString.ty.PointerType #xe ∗
      net.ReadErr (GF := GF) r (interface.mkOk errors.errorString.ty.PointerType #xe) la ra ed err ⊢
      net.ReadErr (GF := GF) r (interface.mkOk errors.errorString.ty.PointerType #xe) la ra ed err ∗
        (⌜err = interface.nil⌝ ∨ (errMsgOk err ∗ crErrId err)) := by
  cases r with
  | bytes bs =>
    simp only [net.ReadErr]
    iintro ⟨-, -, %h⟩; isplitr
    · ipureintro; exact h
    · ileft; ipureintro; exact h
  | eof =>
    simp only [net.ReadErr]
    iintro ⟨#HW, #Hxe, %h⟩; subst h; isplitr
    · ipureintro; rfl
    iright
    isplitl []
    · iapply errMsgOk_of ⟨go.GoType.PointerType errors.errorString.ty, #xe⟩ msg hmsg
      iexact HW
    iunfold crErrId
    ileft
    iexists xe
    iframe Hxe
    ipureintro; rfl
  | err k =>
    simp only [net.ReadErr]
    iintro ⟨-, -, #HE⟩
    iframe HE
    iright
    unfold net.resErr
    icases HE with ⟨%e, #Hop, -⟩
    isplitl []
    · unfold net.opErr
      icases Hop with ⟨%pe, %nw, ⟨%h, -⟩, #Hpe⟩
      subst h
      iunfold errMsgOk
      iexists ⟨go.GoType.PointerType net.OpError.ty, #pe⟩
      isplitr
      · ipureintro; rfl
      imodintro
      iintro %Φ HΦ
      iapply net.wp_OpError_Error pe _ Φ $$ Hpe
      inext
      iintro %m %hm
      iapply HΦ
      ipureintro; exact opErrMsg_read_ne m hm
    iunfold crErrId
    iright
    iexists la, ra, e
    iexact Hop

/-- `cr.hitReadLimit()`. -/
theorem wp_hitReadLimit (cr : Loc) (v : w64) :
    {{ (structFieldRef net.http.connReader go!"remain" cr ↦ v : IProp GF) }}
      (App (Val #(methods (go.GoType.PointerType net.http.connReader.ty) go!"hitReadLimit" #cr))
        (Val #()))
    {{ RET #(decide (sint.Z v ≤ sint.Z (W64 0))); structFieldRef net.http.connReader go!"remain" cr ↦ v }} := by
  wp_start as Hr
  wp_auto
  iapply HΦ $$ Hr

theorem connReader.Read.wp_proof (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG)) :
    connReader.Read.spec (GF := GF) (hG := hG) := by
  intro cr γ t cn a la ra P Q hs Z L c γe r p xs
  wp_start as ⟨⟨%Hc, %HL, %Hrx⟩, #Hcr, #Henv, #Hio, #Hcok, #Hrwc, #Hca, Hst, Hp⟩
  iunfold readEnv at Henv
  icases Henv with ⟨-, %ed, #Hed⟩
  ihave #Hinit := _root_.Perennial.io.isInit_access $$ Hio
  icases Hinit with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  unfold errors.newVar
  icases HEOF with ⟨%xe, #Hxe, -, #HxeE⟩
  icases HUEOF with ⟨%xu, #Hxu, -⟩
  iunfold crHead at Hst
  icases Hst with ⟨Hph, %HrL, %ab, Hcf, Hhb, Hir, Hab, Hrem, Hbuf, Hsend, Hrecv, Hrdl, Hc⟩
  ihave %Hlen := ownSlice_len $$ Hp
  wp_auto
  wp_apply wp_cr_lock cr γ cn P hs Z $$ [$Hcr] as ⟨Hown, ⟨%cv, #Hcond⟩, Hinv⟩
  iunfold crPh at Hinv
  icases Hinv with ⟨%ph, Hph2, Hinv⟩
  ihave %Hag := ghostVar_agree γ.ph _ _ _ _ $$ Hph Hph2
  subst Hag
  simp only [Bool.false_eq_true, ite_false, Hc, decide_false]
  wp_auto
  wp_apply wp_hitReadLimit cr _ $$ [$Hrem] as Hrem
  have hLr : sint.Z (W64 (L - r.length : Nat)) = ((L - r.length : Nat) : Int) := by
    have : ((L - r.length : Nat) : Int) < 2 ^ 63 := by omega
    word
  wp_if_destruct
  · -- the read limit: `io.EOF`
    have hrL : r.length = L := by
      have : ((L - r.length : Nat) : Int) ≤ 0 := by rw [← hLr]; exact Hif
      omega
    ihave Hc2 : (|={⊤}=> monoListLbOwn γe [r] ∗
        ((monoListAuthOwn γe 1 [r] ∗ (readDead (Gg := hG.goose_globalGS) cn true ∨ ⌜r.length = L⌝)) ∨
          monoListAuthOwn γe 1 ([] : List (List w8))) : IProp GF) $$ [Hc]
    · icases Hc with (⟨Hc, Hd⟩ | Hc)
      · imod monoListAuthOwn_update (GF := GF) [r] (List.prefix_refl _) $$ Hc with ⟨Hc, #Hlb⟩
        imodintro; iframe Hlb; ileft; iframe Hc Hd
      · imod monoListAuthOwn_update_app (GF := GF) [r] $$ Hc with ⟨Hc, #Hlb⟩
        simp only [List.nil_append]
        imodintro; iframe Hlb; ileft; iframe Hc; iright; ipureintro; exact hrL
    imod Hc2 with ⟨#Hlb, Hc⟩
    wp_apply wp_cr_unlock cr γ cn P hs Z cv $$ [$Hcr $Hown $Hcond Hph2 Hinv]
    · iunfold crPh; iexists false; simp only [Bool.false_eq_true, ite_false]; iframe Hph2 Hinv
    iapply HΦ
    iexists []
    simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
    iframe Hp
    isplitr
    · ipureintro; exact ⟨by decide, by simp, fun _ => Or.inr (by simp [interface.mkOk])⟩
    isplitr
    · unfold EtcdGrove.io.errAt
      isplitl []
      · iright; imodintro; unfold crHeadErr; iframe Hlb
        isplitl []
        · iapply errMsgOk_of ⟨go.GoType.PointerType errors.errorString.ty, #xe⟩ go!"EOF" (by decide)
          iexact HxeE
        iunfold crErrId
        ileft
        iexists xe
        iframe Hxe
        ipureintro; rfl
      · ipureintro
        intro ii T h _; simp only [interface.mkOk] at h; cases h; exact ⟨xe, rfl⟩
    iunfold crHead
    iframe Hph
    isplitr
    · ipureintro; exact HrL
    iexists ab
    iframe Hcf Hhb Hir Hab Hrem Hbuf Hsend Hrecv Hrdl Hc
  have Hlim := Hif
  wp_if_destruct
  · -- an empty read: at once
    wp_apply wp_cr_unlock cr γ cn P hs Z cv $$ [$Hcr $Hown $Hcond Hph2 Hinv]
    · iunfold crPh; iexists false; simp only [Bool.false_eq_true, ite_false]; iframe Hph2 Hinv
    iapply HΦ
    iexists []
    simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
    iframe Hp
    isplitr
    · ipureintro
      have hx0 : xs.length = 0 := by rw [Hlen.1]; rw [Hif]; rfl
      exact ⟨by decide, by simp, fun h => absurd (List.eq_nil_of_length_eq_zero hx0) h⟩
    isplitr
    · iapply EtcdGrove.io.errAt_nil
    iunfold crHead
    iframe Hph
    isplitr
    · ipureintro; exact HrL
    iexists ab
    iframe Hcf Hhb Hir Hab Hrem Hbuf Hsend Hrecv Hrdl Hc
  have hx0 : 0 < xs.length := by
    rw [Hlen.1]; have h2 := Hlen.2
    have h3 : sint.Z p.len ≠ 0 := fun h => Hif (by word)
    show 0 < (sint.Z p.len).toNat; omega
  have hL0 : 0 < L - r.length := by
    have : ¬ ((L - r.length : Nat) : Int) ≤ 0 := by rw [← hLr]; exact Hlim
    omega
  -- `p` cut at the read limit
  wp_join iprop(∃ (p' : GoSlice) (xs' : List w8), cr_ptr ↦ cr ∗ p_ptr ↦ p' ∗ p' ↦* xs' ∗
      structFieldRef net.http.connReader go!"remain" cr ↦ (W64 (L - r.length : Nat)) ∗
      ⌜0 < xs'.length ∧ xs'.length ≤ xs.length ∧ xs'.length ≤ L - r.length⌝ ∗
      (∀ ys : List w8, ⌜ys.length ≤ xs'.length⌝ -∗ p' ↦* (ys ++ xs'.drop ys.length) -∗
        p ↦* (ys ++ xs.drop ys.length)))
    with [cr p Hp Hrem] as ⟨%p', %xs', cr, p, Hp, Hrem, %Hxs', Hback⟩
  · ihave %Hwf := ownSlice_wf $$ Hp
    have h0 : sint.Z (W64 0) = 0 := rfl
    rw [hLr] at Hif
    have hc : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 (L - r.length : Nat)) ∧ sint.Z (W64 (L - r.length : Nat)) ≤ sint.Z p.cap := by rw [hLr, h0]; omega
    simp only [hc, _root_.and_self, ite_true]
    wp_auto
    ihave Hcut := slice_cut p xs (W64 (L - r.length : Nat)) ⟨by rw [hLr]; omega, by omega⟩ $$ Hp
    icases Hcut with ⟨Hp, Hback⟩
    wp_join_done
    iexists _, _
    iframe cr p Hp Hrem
    have hn : sint.nat (W64 (L - r.length : Nat)) = L - r.length := by show (sint.Z _).toNat = _; rw [hLr]; omega
    isplitr
    · ipureintro
      simp only [List.length_take, hn]
      refine ⟨by omega, by omega, by omega⟩
    iintro %ys %hys Hp
    iapply Hback $$ %ys [] Hp
    ipureintro; simp only [List.length_take, hn] at hys; omega
  · iexists p, xs
    iframe cr p Hp Hrem
    isplitr
    · ipureintro
      have : ¬ ((L - r.length : Nat) : Int) < sint.Z p.len := by rw [← hLr]; exact Hif
      refine ⟨hx0, Nat.le_refl _, ?_⟩
      rw [Hlen.1]; show (sint.Z p.len).toNat ≤ _; omega
    iintro %ys %hys Hp
    iexact Hp
  wp_apply wp_cr_unlock cr γ cn P hs Z cv $$ [$Hcr $Hown $Hcond Hph2 Hinv]
  · iunfold crPh; iexists false; simp only [Bool.false_eq_true, ite_false]; iframe Hph2 Hinv
  ihave %Hplen := ownSlice_len $$ Hp
  -- the connection's `Read` into `p'`
  have hxl : xs'.length = p'.len.toNat := by
    rw [Hplen.1]; have := Hplen.2; unfold sint.nat; word
  ihave HrL := recvTok_L (Gg := hG.goose_globalGS) cn true _ _ $$ Hrecv
  wp_apply +noauto wp_Read t cn true a la ra p' xs' (interface.mkOk errors.errorString.ty.PointerType #xe)
      ed (fun res => iprop(recvTokL (Gg := hG.goose_globalGS) cn true P (r ++ res.got) ∗
        rdlTok (Gg := hG.goose_globalGS) cn true false ∗
        ⌜res.got.length ≤ p'.len.toNat ∧ (res = .bytes [] → p'.len.toNat = 0)⌝ ∗
        ((⌜∀ bs, res ≠ .bytes bs⌝ ∗ monoListAuthOwn γe 1 [r ++ res.got] ∗
            readDead (Gg := hG.goose_globalGS) cn true) ∨
          (⌜∃ bs, res = .bytes bs⌝ ∗ monoListAuthOwn γe 1 ([] : List (List w8))))))
      $$ [Hp HrL Hrdl Hc]
    as %k %err0 ⟨%res, %bs', ⟨HrL, Hrdl, ⟨%Hgl, %Hg0⟩, Hc⟩, Hp, %Hout, HE⟩
  · iframe Hca Hp Hxe Hed
    icases Hc with (⟨Hc, Hd⟩ | Hc)
    · -- the reading is dead: nothing
      icases Hd with (#Hd | %Hd)
      rotate_left
      · exfalso; omega
      imod read_after_dead_au (Gg := hG.goose_globalGS) cn true _ _ p'.len.toNat $$ [$HrL $Hd]
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r' %d' %Hrd HE HD
      imod Hcl $$ %r' %d' %Hrd HE HD with ⟨HrL, ⟨%hg, %hnb⟩⟩
      imodintro
      have hgl := readOutcome_got_le Hrd
      rw [hg, List.append_nil]
      rw [hg] at hgl
      iframe HrL Hrdl
      isplitr
      · ipureintro; exact hgl
      ileft
      iframe Hc Hd
      ipureintro; exact hnb (by omega)
    · imod read_dead_au (Gg := hG.goose_globalGS) cn true _ _ p'.len.toNat false $$ [$HrL $Hrdl]
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r' %d' %Hrd HE HD
      imod Hcl $$ %r' %d' %Hrd HE HD with ⟨HrL, Hrdl, %Hro, Hdead⟩
      obtain ⟨st0, d0, d0', hrdl, Hro⟩ := Hro
      iframe HrL Hrdl
      isplitr
      · ipureintro; exact readOutcome_got_le Hrd
      rcases r' with bs | _ | (_ | _ | _)
      · iright; iframe Hc; ipureintro; exact ⟨bs, rfl⟩
      rotate_left 2
      · exact absurd Hro (fun h => readOutcome_no_timeout hrdl h)
      all_goals (
        ihave #Hd : readDead (Gg := hG.goose_globalGS) cn true $$ [Hdead]
        · iapply Hdead; ipureintro; simp
        imod monoListAuthOwn_update_app (GF := GF) [r] $$ Hc with ⟨Hc, -⟩
        imodintro
        ileft
        simp only [ReadRes.got, List.append_nil, List.nil_append]
        iframe Hc Hd
        ipureintro; intro bs h; cases h)
  ihave %Hptr := readErr_ptrTyped res la ra ed err0 xe $$ HE
  icases readErr_msgOk res la ra ed err0 xe go!"EOF" (by decide) $$ [$HxeE $Hxe $HE] with ⟨HE, #Hem⟩
  ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn true _ _ $$ HrL
  wp_auto_lc 1
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrT with HrT
  ihave Hsum : (∃ ys : List w8, ⌜sint.Z k = ys.length ∧ ys.length ≤ xs'.length ∧
        (ys ≠ [] ∨ err0 ≠ interface.nil)⌝ ∗
      p' ↦* (ys ++ xs'.drop ys.length) ∗ recvTok (Gg := hG.goose_globalGS) cn true P (r ++ ys) ∗
      ((⌜err0 ≠ interface.nil⌝ ∗ monoListAuthOwn γe 1 [r ++ ys] ∗
          readDead (Gg := hG.goose_globalGS) cn true) ∨
        (⌜err0 = interface.nil⌝ ∗ monoListAuthOwn γe 1 ([] : List (List w8)))) : IProp GF)
      $$ [Hp HrT Hc HE]
  · rcases res with bs | _ | k0
    · -- bytes: no error
      simp only [net.ReadErr]
      icases HE with %Herr
      obtain ⟨hk, rfl⟩ := Hout
      simp only [ReadRes.got] at Hgl ⊢
      have hbl : bs.length ≤ xs'.length := by rw [hxl]; exact Hgl
      have hb1 : 1 ≤ bs.length := by
        rcases bs with _ | ⟨x, bs⟩
        · exfalso
          have := Hg0 rfl
          omega
        · simp
      iexists bs
      rw [List.take_of_length_le hbl]
      iframe Hp HrT
      icases Hc with (⟨%Hnb, -⟩ | ⟨-, Hc⟩)
      · exact absurd rfl (Hnb bs)
      isplitr
      · ipureintro
        refine ⟨?_, hbl, Or.inl (by rintro rfl; simp at hb1)⟩
        rw [Nat.min_eq_right hbl] at hk
        word
      iright; iframe Hc; ipureintro; exact Herr
    all_goals (
      obtain ⟨hk, rfl⟩ := Hout
      ihave %Hne : ⌜err0 ≠ interface.nil⌝ $$ [HE]
      · simp only [net.ReadErr]
        first
        | (icases HE with %h; ipureintro; rw [h]; simp [interface.mkOk])
        | (ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
           obtain ⟨-, Hne⟩ := Hnet
           obtain ⟨pe, rfl⟩ := Hne (by simp)
           ipureintro; simp [interface.mkOk])
      iexists []
      simp only [ReadRes.got, List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
      iframe Hp HrT
      icases Hc with (⟨-, Hc, #Hd⟩ | ⟨%Hb, -⟩)
      rotate_left
      · obtain ⟨bs, hb⟩ := Hb; cases hb
      isplitr
      · ipureintro; exact ⟨by rw [hk]; rfl, by simp, Or.inr Hne⟩
      ileft; iframe Hc Hd; ipureintro; exact Hne)
  icases Hsum with ⟨%ys, ⟨%Hn, %Hyl, %Hprog⟩, Hp, Hrecv, Hc⟩
  -- under the mutex: `inRead` cleared, an error's context cancellation, the limit lowered
  wp_apply wp_cr_lock cr γ cn P hs Z $$ [$Hcr] as ⟨Hown, ⟨%cv', #Hcond'⟩, Hinv⟩
  iunfold crPh at Hinv
  icases Hinv with ⟨%ph, Hph2, Hinv⟩
  ihave %Hag := ghostVar_agree γ.ph _ _ _ _ $$ Hph Hph2
  subst Hag
  simp only [Bool.false_eq_true, ite_false]
  wp_join iprop(cr_ptr ↦ cr ∗ err_ptr ↦ err0 ∗
      structFieldRef net.http.connReader go!"conn" cr ↦ c)
    at next with [cr err Hcf] as ⟨cr, err, Hcf⟩
  · rcases err0 with i | _
    · wp_auto
      wp_apply wp_handleReadErrorLocked cr c _ $$ [$Hcf $Hcok] as Hcf
      wp_join_done
    · wp_auto
      wp_join_done
  have hn' : (W64 (L - r.length : Nat) - k : w64) = W64 (L - (r ++ ys).length : Nat) := by
    have h1 : ((L - r.length : Nat) : Int) < 2 ^ 62 := by omega
    have h2 : ((L - (r ++ ys).length : Nat) : Int) = ((L - r.length : Nat) : Int) - ys.length := by
      simp only [List.length_append]; omega
    have hz : sint.Z k = ys.length := Hn
    have hyl : (ys.length : Int) ≤ ((L - r.length : Nat) : Int) := by
      have := Hxs'.2.2; omega
    rw [h2]
    word
  rw [hn']
  wp_apply wp_cr_unlock cr γ cn P hs Z cv' $$ [$Hcr $Hown $Hcond' Hph2 Hinv]
  · iunfold crPh; iexists false; simp only [Bool.false_eq_true, ite_false]; iframe Hph2 Hinv
  iunfold crCond at Hcond'
  icases Hcond' with ⟨-, #Hcf', #Hcv⟩
  wp_auto
  ihave Hc2 : (|={⊤}=> (⌜err0 = interface.nil⌝ ∨ monoListLbOwn γe [r ++ ys]) ∗
      ((monoListAuthOwn γe 1 [r ++ ys] ∗
          (readDead (Gg := hG.goose_globalGS) cn true ∨ ⌜(r ++ ys).length = L⌝)) ∨
        monoListAuthOwn γe 1 ([] : List (List w8))) : IProp GF) $$ [Hc]
  · icases Hc with (⟨%Hne, Hc, #Hd⟩ | ⟨%He, Hc⟩)
    · imod monoListAuthOwn_update (GF := GF) [r ++ ys] (List.prefix_refl _) $$ Hc with ⟨Hc, #Hlb⟩
      imodintro
      isplitr
      · iright; iexact Hlb
      ileft; iframe Hc; ileft; iexact Hd
    · imodintro
      isplitr
      · ileft; ipureintro; exact He
      iright; iexact Hc
  imod Hc2 with ⟨#Hlb, Hc⟩
  wp_apply sync.Cond.wp_Broadcast $$ [$Hcv]
  iapply HΦ
  iexists ys
  ihave Hp := Hback $$ %ys %Hyl Hp
  iframe Hp
  isplitr
  · ipureintro
    exact ⟨Hn, Nat.le_trans Hyl Hxs'.2.1, fun _ => Hprog⟩
  isplitr
  · unfold EtcdGrove.io.errAt
    isplitl []
    · icases Hlb with (%h | #Hlb)
      · ileft; ipureintro; exact h
      · icases Hem with (%h | #Hem)
        · ileft; ipureintro; exact h
        · iright; imodintro; unfold crHeadErr; iframe Hlb; iexact Hem
    · ipureintro; exact Hptr.1
  iunfold crHead
  iframe Hph
  isplitr
  · ipureintro; simp only [List.length_append]; omega
  iexists ab
  iframe Hcf Hhb Hir Hab Hrem Hbuf Hsend Hrecv Hrdl Hc

end proof

end net.http
end Perennial
