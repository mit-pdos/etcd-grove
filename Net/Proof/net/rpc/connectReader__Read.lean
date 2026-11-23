/-
The proof of `connectReader.Read` (`Net/Spec/net/rpc/connectReader__Read.lean`): the connection's
`Read` (`net.Conn.Read.spec` with the library's `read_au`), into `p` while `cr` has not failed, into
a buffer of its own after; the bytes' protocol fact a step later (a later credit) and, the dialer
having written no request, a prefix of the answer (`resp_before_req`, a second credit). A first
error records `cr`'s failure in its once-cell.
-/
module

public import Net.Spec.net.rpc.connectReader__Read
public import Net.Spec.net.Conn__Read
public import GooseLang.Ext.Net.Stream

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
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A read error of the connection is a pointer (`io.ptrTyped`): `io.EOF`'s `*errorString`, or an
`*OpError`. -/
theorem readErr_ptr (r : ReadRes) (la ra ed err : GoInterface) (xe : Loc) :
    net.ReadErr (GF := GF) r (interface.mkOk errors.errorString.ty.PointerType #xe) la ra ed err ⊢
      ⌜_root_.Perennial.io.ptrTyped err⌝ := by
  cases r with
  | bytes bs =>
    simp only [net.ReadErr]
    iintro %h; subst h; ipureintro; exact _root_.Perennial.io.ptrTyped_nil
  | eof =>
    simp only [net.ReadErr]
    iintro %h; subst h; ipureintro
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
    intro ii T h hT
    simp only [interface.mkOk] at h
    cases h; exact ⟨pe, rfl⟩

theorem connectReader.Read.wp_proof (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG)) :
    connectReader.Read.spec (GF := GF) (hG := hG) := by
  intro W a cn γ cr t la ra γe r p xs ed
  wp_start as ⟨%HhsA, #Hio, #Hed, #Hat, Hst, Hp⟩
  ihave #Hinit := _root_.Perennial.io.isInit_access $$ Hio
  icases Hinit with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  unfold errors.newVar
  icases HEOF with ⟨%xe, #Hxe, -⟩
  icases HUEOF with ⟨%xu, #Hxu, -⟩
  iunfold crAt at Hat
  icases Hat with ⟨#Hr, #Hconn⟩
  iunfold crSt at Hst
  icases Hst with ⟨%f, %R, Hf, Hrecv, #Hrpc, Hh, ⟨%Hr1, %Hr2⟩, Hc⟩
  ihave %Hlen := ownSlice_len $$ Hp
  wp_auto
  wp_if_destruct
  · -- an empty read: at once
    iapply HΦ
    iexists []
    simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
    iframe Hp
    isplitr
    · ipureintro
      have hx0 : xs.length = 0 := by rw [Hlen.1]; rw [Hif]; rfl
      exact ⟨by simp, by simp, fun h => absurd (List.eq_nil_of_length_eq_zero hx0) h⟩
    isplitr
    · iapply EtcdGrove.io.errAt_nil
    iunfold crSt
    iexists f, R
    iframe Hf Hrecv Hrpc Hh Hc
    ipureintro; exact ⟨Hr1, Hr2⟩
  have hp0 : 0 < xs.length := by
    rw [Hlen.1]
    have h2 := Hlen.2
    word
  cases f with
  | true =>
    -- failed: read into a buffer of its own, deliver nothing
    icases Hc with (⟨-, Hc⟩ | ⟨⟨%Hf, -⟩, -⟩)
    rotate_left
    · cases Hf
    imod monoListAuthOwn_update (GF := GF) [r] (List.prefix_refl _) $$ Hc with ⟨Hc, #Hlb⟩
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) p.len) as %q ⟨Hq, -⟩
    · ipureintro; exact Hlen.2
    ihave HrL := recvTok_L (Gg := hG.goose_globalGS) cn false _ _ $$ Hrecv
    wp_apply +noauto wp_Read t cn false a la ra q _ (interface.mkOk errors.errorString.ty.PointerType #xe)
        ed (fun res => recvTokL (Gg := hG.goose_globalGS) cn false (respProto W a) (R ++ res.got))
        $$ [Hq HrL]
      as %k %err ⟨%res, %bs', HrL, Hq, %Hout, HE⟩
    · iframe Hconn Hq Hxe Hed
      imod read_au (Gg := hG.goose_globalGS) cn false _ _ q.len.toNat $$ HrL
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r' %d' %Hrd HE HD
      imod Hcl $$ %r' %d' %Hrd HE HD with ⟨HP, -⟩
      imodintro
      iexact HP
    ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn false _ _ $$ HrL
    -- the error's shape: `nil` for bytes, else a pointer
    ihave %Herr : ⌜err = interface.nil ∨ ∃ (T : go.GoType) (l : Loc), err = interface.mkOk (go.GoType.PointerType T) #l⌝
        $$ [HE]
    · rcases res with bs | _ | k0
      · simp only [net.ReadErr]; icases HE with %h; ipureintro; exact Or.inl h
      · simp only [net.ReadErr]; icases HE with %h; ipureintro; exact Or.inr ⟨_, xe, h⟩
      · simp only [net.ReadErr]
        ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
        obtain ⟨-, Hne⟩ := Hnet
        obtain ⟨pe, rfl⟩ := Hne (by simp)
        ipureintro; exact Or.inr ⟨_, pe, rfl⟩
    -- the result: no byte, the error (or `io.ErrUnexpectedEOF`), once the protocol fact is out
    ihave Hpost : (£ 1 -∗ £ 1 -∗ |={⊤}=> ∀ e : GoInterface,
        ⌜∃ (T : go.GoType) (l : Loc), e = interface.mkOk (go.GoType.PointerType T) #l⌝ -∗
        Φ (PairV #(W64 0) #e)) $$ [Hp Hf HrT Hh HΦ Hc]
    · iintro Hlc1 Hlc2
      imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrT with HrT
      icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ HrT with ⟨HrT, #Hpp⟩
      imod resp_before_req W a cn γ _ $$ [$Hrpc $Hh $Hlc2 $Hpp] with ⟨Hh, %Hpre⟩
      rw [HhsA, show hsErr connectAns = badReqAns from ite_eq_left rfl] at Hpre
      imodintro
      iintro %e %He
      iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
      iframe Hp
      isplitr
      · ipureintro
        obtain ⟨T, l, rfl⟩ := He
        exact ⟨by simp, by simp, fun _ => Or.inr (by simp [interface.mkOk])⟩
      isplitr
      · unfold EtcdGrove.io.errAt
        isplitl []
        · iright; imodintro; iunfold crErr; iexact Hlb
        · ipureintro
          obtain ⟨T, l, rfl⟩ := He
          intro ii T' h _; simp only [interface.mkOk] at h; cases h; exact ⟨l, rfl⟩
      iunfold crSt
      iexists true, (R ++ res.got)
      iframe Hf HrT Hrpc Hh
      isplitr
      · ipureintro
        exact ⟨Hr1.trans (List.prefix_append _ _), Hpre⟩
      ileft
      isplitr
      · ipureintro; rfl
      iexact Hc
    wp_auto_lc 2
    iapply fupd_wp
    imod Hpost $$ Hlc1 Hlc2 with Hpost
    imodintro
    rcases Herr with Herr | ⟨T, l, Herr⟩
    · rw [Herr]
      wp_auto
      iapply Hpost
      ipureintro; exact ⟨_, xu, rfl⟩
    · rw [Herr]
      wp_auto
      iapply Hpost
      ipureintro; exact ⟨T, l, rfl⟩
  | false =>
    -- not failed: read into `p`
    icases Hc with (⟨%Hf, -⟩ | ⟨⟨-, %HR⟩, Hc⟩)
    · cases Hf
    rw [HR]
    wp_auto
    ihave HrL := recvTok_L (Gg := hG.goose_globalGS) cn false _ _ $$ Hrecv
    wp_apply +noauto wp_Read t cn false a la ra p xs (interface.mkOk errors.errorString.ty.PointerType #xe)
        ed (fun res => iprop(recvTokL (Gg := hG.goose_globalGS) cn false (respProto W a) (r ++ res.got) ∗
          ⌜res.got.length ≤ p.len.toNat ∧ (res = .bytes [] → p.len.toNat = 0)⌝))
        $$ [Hp HrL]
      as %k %err ⟨%res, %bs', ⟨HrL, ⟨%Hgl, %Hg0⟩⟩, Hp, %Hout, HE⟩
    · iframe Hconn Hp Hxe Hed
      imod read_au (Gg := hG.goose_globalGS) cn false _ _ p.len.toNat $$ HrL
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r' %d' %Hrd HE HD
      imod Hcl $$ %r' %d' %Hrd HE HD with ⟨HP, -⟩
      imodintro
      iframe HP
      ipureintro; exact readOutcome_got_le Hrd
    ihave %Hptr := readErr_ptr res la ra ed err xe $$ HE
    ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn false _ _ $$ HrL
    wp_auto_lc 2
    iapply fupd_wp
    imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrT with HrT
    icases recvTok_proto (Gg := hG.goose_globalGS) cn false _ _ $$ HrT with ⟨HrT, #Hpp⟩
    imod resp_before_req W a cn γ _ $$ [$Hrpc $Hh $Hlc2 $Hpp] with ⟨Hh, %Hpre⟩
    rw [HhsA, show hsErr connectAns = badReqAns from ite_eq_left rfl] at Hpre
    imodintro
    have hxl : xs.length = p.len.toNat := by
      rw [Hlen.1]; have := Hlen.2; unfold sint.nat; word
    rcases res with bs | _ | k0
    · -- bytes: no error
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      obtain ⟨hk, rfl⟩ := Hout
      simp only [ReadRes.got] at Hgl Hpre ⊢
      have hbl : bs.length ≤ xs.length := by rw [hxl]; exact Hgl
      have hb1 : 1 ≤ bs.length := by
        rcases bs with _ | ⟨x, bs⟩
        · exfalso
          have := Hg0 rfl
          omega
        · simp
      wp_auto
      iapply HΦ
      iexists bs
      rw [List.take_of_length_le hbl]
      iframe Hp
      isplitr
      · ipureintro
        refine ⟨?_, hbl, fun _ => Or.inl (by rintro rfl; simp at hb1)⟩
        rw [Nat.min_eq_right hbl] at hk
        word
      isplitr
      · iapply EtcdGrove.io.errAt_nil
      iunfold crSt
      iexists false, (r ++ bs)
      iframe Hf HrT Hrpc Hh
      isplitr
      · ipureintro; exact ⟨List.prefix_refl _, Hpre⟩
      iright
      iframe Hc
      ipureintro; exact ⟨rfl, rfl⟩
    all_goals (
      obtain ⟨hk, rfl⟩ := Hout
      simp only [ReadRes.got, List.append_nil] at Hpre ⊢
      ihave %Herr : ⌜∃ (T : go.GoType) (l : Loc), err = interface.mkOk (go.GoType.PointerType T) #l⌝
          $$ [HE]
      · simp only [net.ReadErr]
        first
        | (icases HE with %h; ipureintro; exact ⟨_, xe, h⟩)
        | (ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
           obtain ⟨-, Hne⟩ := Hnet
           obtain ⟨pe, rfl⟩ := Hne (by simp)
           ipureintro; exact ⟨_, pe, rfl⟩)
      obtain ⟨T, l, Herr⟩ := Herr
      imod monoListAuthOwn_update_app (GF := GF) [r] $$ Hc with ⟨Hc, #Hlb⟩
      simp only [List.nil_append]
      rw [Herr]
      wp_auto
      iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
      iframe Hp
      isplitr
      · ipureintro
        exact ⟨by rw [hk]; rfl, by simp, fun _ => Or.inr (by simp [interface.mkOk])⟩
      isplitr
      · unfold EtcdGrove.io.errAt
        isplitl []
        · iright; imodintro; iunfold crErr; iexact Hlb
        · ipureintro
          rw [← Herr]; exact Hptr
      iunfold crSt
      iexists true, r
      iframe HrT Hrpc Hh Hf
      isplitr
      · ipureintro; exact ⟨List.prefix_refl _, Hpre⟩
      ileft
      isplitr
      · ipureintro; rfl
      iexact Hc)

end proof

end net.rpc
end Perennial
