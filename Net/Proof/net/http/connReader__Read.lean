/-
The proof of `connReader.Read` (`Net/Spec/net/http/connReader__Read.lean`) in the head phase: under
the mutex the phase is the main one (the main thread's half of `γ.ph`), so the main thread owns the
fields; at the read limit `io.EOF`, an empty `p` at once, else `p` cut at the limit, `inRead` set and
the mutex released; the connection's `Read` (`net.Conn.Read.spec` with the library's `read_au`) into
`p`, or, past a read error, into a buffer of its own (nothing delivered, the reader's token past what
was delivered); then under the mutex `inRead` cleared, an error recorded (`failed`, the connection's
context canceled: `handleReadErrorLocked`), the limit lowered, and the condition variable broadcast.
-/
module

public import Net.Spec.net.http.connReader__Read
public import Net.Spec.net.Conn__Read
public import Net.Proof.net.http.ConnReaderLemmas
public import Proof.bufio.Base
public import GooseLang.Ext.Net.Proto

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
  intro cr γ t cn a la ra P Q hs Z L c r p xs
  wp_start as ⟨⟨%Hc, %HL, %Hrx⟩, #Hcr, #Henv, #Hio, #Hcok, #Hrwc, #Hca, Hst, Hp⟩
  iunfold readEnv at Henv
  icases Henv with ⟨-, %ed, #Hed⟩
  ihave #Hinit := _root_.Perennial.io.isInit_access $$ Hio
  icases Hinit with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  unfold errors.newVar
  icases HEOF with ⟨%xe, #Hxe, -⟩
  icases HUEOF with ⟨%xu, #Hxu, -⟩
  iunfold crHead at Hst
  icases Hst with ⟨Hph, %HrL, %ab, %fl, Hcf, Hhb, Hir, Hab, Hfl, Hrem, Hbuf, Hsend, %R, Hrecv, %HrR⟩
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
      · iright; imodintro; unfold crHeadErr; itrivial
      · ipureintro
        intro ii T h _; simp only [interface.mkOk] at h; cases h; exact ⟨xe, rfl⟩
    iunfold crHead
    iframe Hph
    isplitr
    · ipureintro; exact HrL
    iexists ab, fl
    iframe Hcf Hhb Hir Hab Hfl Hrem Hbuf Hsend
    iexists R
    iframe Hrecv
    ipureintro; exact HrR
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
    iexists ab, fl
    iframe Hcf Hhb Hir Hab Hfl Hrem Hbuf Hsend
    iexists R
    iframe Hrecv
    ipureintro; exact HrR
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
    simp only [hc, and_self, ite_true]
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
  -- the connection's `Read`: into `p'`, or past a failure into a buffer of the reader's own
  wp_join iprop(∃ (n : w64) (e : GoInterface) (ys R' : List w8), cr_ptr ↦ cr ∗ p_ptr ↦ p' ∗
      n_ptr ↦ n ∗ err_ptr ↦ e ∗ p' ↦* (ys ++ xs'.drop ys.length) ∗
      recvTok (Gg := hG.goose_globalGS) cn true P R' ∗
      ⌜sint.Z n = ys.length ∧ ys.length ≤ xs'.length ∧ (ys ≠ [] ∨ e ≠ interface.nil) ∧
        r ++ ys <+: R' ∧ ((fl = false ∧ e = interface.nil) → R' = r ++ ys) ∧
        _root_.Perennial.io.ptrTyped e⌝)
    with [cr p n err Hp Hrecv] as ⟨%n, %e, %ys, %R', cr, p, n, err, Hp, Hrecv, %Hys⟩
  · -- not failed: into `p'`
    have HR : R = r := HrR.2 rfl
    rw [HR]
    ihave HrL := recvTok_L (Gg := hG.goose_globalGS) cn true _ _ $$ Hrecv
    wp_apply +noauto wp_Read t cn true a la ra p' xs' (interface.mkOk errors.errorString.ty.PointerType #xe)
        ed (fun res => iprop(recvTokL (Gg := hG.goose_globalGS) cn true P (r ++ res.got) ∗
          ⌜res.got.length ≤ p'.len.toNat ∧ (res = .bytes [] → p'.len.toNat = 0)⌝))
        $$ [Hp HrL]
      as %k %err0 ⟨%res, %bs', ⟨HrL, ⟨%Hgl, %Hg0⟩⟩, Hp, %Hout, HE⟩
    · iframe Hca Hp Hxe Hed
      imod read_au (Gg := hG.goose_globalGS) cn true _ _ p'.len.toNat $$ HrL
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r' %d' %Hrd HE HD
      imod Hcl $$ %r' %d' %Hrd HE HD with ⟨HP, -⟩
      imodintro
      iframe HP
      ipureintro; exact readOutcome_got_le Hrd
    ihave %Hptr := readErr_ptrTyped res la ra ed err0 xe $$ HE
    ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn true _ _ $$ HrL
    wp_auto
    have hxl : xs'.length = p'.len.toNat := by
      rw [Hplen.1]; have := Hplen.2; unfold sint.nat; word
    wp_join_done
    rcases res with bs | _ | k0
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
      iexists k, err0, bs, (r ++ bs)
      rw [List.take_of_length_le hbl]
      iframe cr p n err Hp HrT
      ipureintro
      refine ⟨?_, hbl, Or.inl (by rintro rfl; simp at hb1), List.prefix_refl _, fun _ => rfl, Hptr.1⟩
      rw [Nat.min_eq_right hbl] at hk
      word
    all_goals (
      obtain ⟨hk, rfl⟩ := Hout
      simp only [ReadRes.got, List.append_nil]
      iexists k, err0, [], r
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
      iframe cr p n err Hp HrT
      ihave %Hne : ⌜err0 ≠ interface.nil⌝ $$ [HE]
      · simp only [net.ReadErr]
        first
        | (icases HE with %h; ipureintro; rw [h]; simp [interface.mkOk])
        | (ihave %Hnet := net.resErr_netErr _ _ _ _ _ _ _ $$ HE
           obtain ⟨-, Hne⟩ := Hnet
           obtain ⟨pe, rfl⟩ := Hne (by simp)
           ipureintro; simp [interface.mkOk])
      ipureintro
      exact ⟨by rw [hk]; rfl, by simp, Or.inr Hne, List.prefix_refl _, fun _ => trivial, Hptr.1⟩)
  · -- failed: a buffer of the reader's own, nothing delivered
    wp_apply (wp_slice_make2 (V := w8) p'.len) as %q ⟨Hq, -⟩
    · ipureintro; exact Hplen.2
    ihave HrL := recvTok_L (Gg := hG.goose_globalGS) cn true _ _ $$ Hrecv
    wp_apply +noauto wp_Read t cn true a la ra q _ (interface.mkOk errors.errorString.ty.PointerType #xe)
        ed (fun res => recvTokL (Gg := hG.goose_globalGS) cn true P (R ++ res.got))
        $$ [Hq HrL]
      as %k %err0 ⟨%res, %bs', HrL, Hq, %Hout, HE⟩
    · iframe Hca Hq Hxe Hed
      imod read_au (Gg := hG.goose_globalGS) cn true _ _ q.len.toNat $$ HrL
        with ⟨%st, %d, HE, HD, Hcl⟩
      imodintro
      iexists st, d
      iframe HE HD
      iintro %r' %d' %Hrd HE HD
      imod Hcl $$ %r' %d' %Hrd HE HD with ⟨HP, -⟩
      imodintro
      iexact HP
    ihave %Hptr := readErr_ptrTyped res la ra ed err0 xe $$ HE
    ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn true _ _ $$ HrL
    wp_auto
    rcases err0 with _ | i
    · wp_auto
      wp_join_done
      iexists (W64 0), _, [], (R ++ res.got)
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
      iframe cr p n err Hp HrT
      ipureintro
      refine ⟨by decide, by simp, ?_, HrR.1.trans (List.prefix_append _ _), ?_, Hptr.1⟩ <;> simp
    · wp_auto
      wp_join_done
      iexists (W64 0), _, [], (R ++ res.got)
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
      iframe cr p n err Hp HrT
      ipureintro
      refine ⟨by decide, by simp, ?_, HrR.1.trans (List.prefix_append _ _), ?_, ?_⟩
      · simp [interface.mkOk]
      · simp
      · intro ii T h _; simp only [interface.mkOk] at h; cases h; exact ⟨xu, rfl⟩
  -- under the mutex: `inRead` cleared, an error recorded, the limit lowered
  obtain ⟨Hn, Hyl, Hprog, HrR', HR', Hptr⟩ := Hys
  wp_apply wp_cr_lock cr γ cn P hs Z $$ [$Hcr] as ⟨Hown, ⟨%cv', #Hcond'⟩, Hinv⟩
  iunfold crPh at Hinv
  icases Hinv with ⟨%ph, Hph2, Hinv⟩
  ihave %Hag := ghostVar_agree γ.ph _ _ _ _ $$ Hph Hph2
  subst Hag
  simp only [Bool.false_eq_true, ite_false]
  wp_join iprop(∃ fl' : Bool, cr_ptr ↦ cr ∗ err_ptr ↦ e ∗
      structFieldRef net.http.connReader go!"conn" cr ↦ c ∗
      structFieldRef net.http.connReader go!"failed" cr ↦ fl' ∗
      ⌜fl' = false → fl = false ∧ e = interface.nil⌝)
    at next with [cr err Hcf Hfl] as ⟨%fl', cr, err, Hcf, Hfl, %Hfl'⟩
  · rcases e with i | _
    · wp_auto
      wp_apply wp_handleReadErrorLocked cr c _ $$ [$Hcf $Hcok] as Hcf
      wp_join_done
      iexists true
      iframe cr err Hcf Hfl
      ipureintro; intro h; cases h
    · wp_auto
      wp_join_done
      iexists fl
      iframe cr err Hcf Hfl
      ipureintro; intro h
      exact ⟨h, rfl⟩
  have hn' : (W64 (L - r.length : Nat) - n : w64) = W64 (L - (r ++ ys).length : Nat) := by
    have h1 : ((L - r.length : Nat) : Int) < 2 ^ 62 := by omega
    have h2 : ((L - (r ++ ys).length : Nat) : Int) = ((L - r.length : Nat) : Int) - ys.length := by
      simp only [List.length_append]; omega
    have hz : sint.Z n = ys.length := Hn
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
  wp_apply sync.Cond.wp_Broadcast $$ [$Hcv]
  iapply HΦ
  iexists ys
  ihave Hp := Hback $$ %ys %Hyl Hp
  iframe Hp
  isplitr
  · ipureintro
    refine ⟨Hn, Nat.le_trans Hyl Hxs'.2.1, fun _ => ?_⟩
    exact Hprog
  isplitr
  · unfold EtcdGrove.io.errAt
    isplitl []
    · rcases e with i | _
      · iright; imodintro; unfold crHeadErr; itrivial
      · ileft; ipureintro; rfl
    · ipureintro; exact Hptr
  iunfold crHead
  iframe Hph
  isplitr
  · ipureintro; simp only [List.length_append]; omega
  iexists ab, fl'
  iframe Hcf Hhb Hir Hab Hfl Hrem Hbuf Hsend
  iexists R'
  iframe Hrecv
  ipureintro
  exact ⟨HrR', fun h => HR' (Hfl' h)⟩

end proof

end net.http
end Perennial
