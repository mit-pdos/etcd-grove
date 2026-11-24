/-
The craq kit's configuration messages (`kit.go`; lab `Kit/OrchConf.lean`, `Decode.lean`,
`Await.lean`, `OrchSend.lean`, notes/dsv-craq.md, P4 (c)), proved over the net extension's
canonical `net` specs (`Net/Spec/net/`, taken as hypotheses, as paxos's `NetProof.lean`) and the
address-protocol laws of `GooseLang/Ext/Net/Proto.lean` (`dial_au`, `listen_au`, `accept_au`,
`write_acc`, `read_au`, `close_au`).

* The configuration addresses' protocol is trivial (`confProto`: the bytes mean nothing; a
  machine trusts only what `decode` checks).
* `wp_rnd`, `wp_choose` (`confOk`), `wp_plan` (`planOk`), `wp_mine` (a sublist),
  `wp_Conf_encode` (eight bytes), `wp_Conf_String`, `wp_decode` (`ok` only for a `msgOk`
  message);
* `wp_sendConf`: `net.Dial`, `Write`, `io.ReadFull` of the one-byte answer, `Close`: some Boolean;
* `wp_configure`: every client machine's and chain machine `2..N+1`'s configuration address, each
  until acknowledged (`log.Println` through `LogHyp`, H6);
* `wp_awaitConf`: `net.Listen` retried, the `Accept` loop, `io.ReadFull` of eight bytes, `decode`,
  the first accepted message sent on a bag channel of `msgOk` (`isChanBag`), the acknowledgment;
  it never returns; `wp_recv_msg`: what `<-ch` receives from such a channel is `msgOk`;
  `wp_make_conf_chan`: `make(chan msg, 1)` gives such a channel.
* Helpers: `kit_net_init` (the package facts the net specs name, from the kit's
  initialization), `close_upd` (`Close`'s update), `confAddrs_proto`, the pointer-receiver
  forms `wp_Conf_String_ptr`, `wp_Conf_encode_ptr`.

`io.ReadFull` over a connection: Perennial's `io.ReadFull.spec` (at the pin `7b2259a12`) asks the
reader's condition of an empty read (`notes/perennial-changes.md`, 2026-11-23, "ReadAtLeast's
premise"), which a connection's (`net.conn_readerOk`: `0 < len(p)`) refuses. `wp_ReadAtLeast_lt`
and `wp_ReadFull_lt` here are Perennial's proofs of the translated `io.ReadAtLeast`/`io.ReadFull`
with the premise asked only of the reads the loop makes (Perennial branch `readatleast-prefix`,
`af905abba`, not landed): proofs of the code, no trust added; drop them on the pin bump.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.KitDefs
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Conf
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.LogHyp
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pkg
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Proof.net.AtAddr
public import Net.Proof.net.ConnIo
public import Perennial.Spec.io.ReadAtLeast
public import Perennial.Proof.time.Link
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.despreston.go_craq.examples.craqnet

open EtcdGrove github_com.despreston.go_craq


/-! ### `io.ReadAtLeast`/`io.ReadFull` asking the reader's condition only of the reads they make

Perennial's proofs (`Perennial/Proof/io/ReadAtLeast.lean`, `ReadFull.lean` at `7b2259a12`), with
the premise of Perennial branch `readatleast-prefix` (`af905abba`): `Pre` only after `ys` with
`len(ys) < min` and `len(ys) < len(buf)`. -/

section io
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.io.Assumptions]

theorem wp_ReadAtLeast_lt :
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r0 : List w8) (p : GoSlice) (xs : List w8)
    (min : w64) (eof ueof sb : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ io.readerOk ri Pre S E ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      globalAddr io.ErrShortBuffer ↦□ sb ∗
      ⌜∀ ys : List w8, (ys.length : Int) < sint.Z min ∧ ys.length < xs.length →
        Pre (r0 ++ ys) (xs.length - ys.length)⌝ ∗
      S r0 ∗ p ↦* xs }}
    (App (App (App (Val (@! io.ReadAtLeast)) (Val #(interface.ok ri))) (Val #p)) (Val #min))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ S (r0 ++ ys) ∗
        io.readAtLeastRes E eof ueof sb r0 ys xs.length (sint.Z min) err }} := by
  intro ri Pre S E r0 p xs min eof ueof sb
  wp_start as ⟨#Hr, #Heof, #Hueof, #Hsb, %Hpre, HS, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hp
  ihave %Hwf := ownSlice_wf $$ Hp
  -- `EOF`'s value is a `*errorString`
  ihave HEOF := io.eof_of_init $$ Hpkg
  iunfold errors.newVar at HEOF
  icases HEOF with ⟨%xeof, #HEOF, -⟩
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ Heof HEOF
  subst Heq
  wp_auto
  wp_if_destruct
  · -- `len(buf) < min`: `ErrShortBuffer`
    iapply HΦ
    iexists []
    simp only [List.nil_append, List.drop_zero, List.append_nil, List.length_nil]
    iframe Hp HS
    isplit
    · ipureintro; exact ⟨by word, by omega⟩
    unfold io.readAtLeastRes
    ileft; ipureintro
    exact ⟨by word, rfl, rfl⟩
  have Hmin : sint.Z min ≤ (xs.length : Int) := by word
  ihave HI : (∃ (n : w64) (ev : GoInterface) (ys : List w8),
      "n" ∷ n_ptr ↦ n ∗ "err" ∷ err_ptr ↦ ev ∗
      "Hp" ∷ p ↦* (ys ++ xs.drop ys.length) ∗ "HS" ∷ S (r0 ++ ys) ∗
      "#Herr" ∷ io.errAt E (r0 ++ ys) ev ∗ "%Hty" ∷ ⌜io.ptrTyped ev⌝ ∗
      "%Hys" ∷ ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ : IProp GF) $$ [n err Hp HS]
  · iexists _, _, []
    simp only [List.nil_append, List.drop_zero, List.append_nil, List.length_nil]
    iframe
    isplit
    · unfold io.errAt; ileft; ipureintro; rfl
    ipureintro
    exact ⟨io.ptrTyped_nil, by simp only [zero_val, ZeroVal.zeroValDef]; word, by omega⟩
  wp_for HI
  wp_if_destruct
  · -- `n < min`
    rcases ev with ei | _
    rotate_left
    · -- `err == nil`: another `Read` of `buf[n:]`
      wp_auto
      simp only [decide_eq_true_eq, ↓reduceIte]
      wp_auto
      have Hb : 0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z p.len ∧ sint.Z p.len ≤ sint.Z p.cap := by
        refine ⟨by omega, by omega, ?_⟩; exact Hwf.2
      simp only [Hb, _root_.and_self, ↓reduceIte]
      ihave %Hlen' := ownSlice_len $$ Hp
      icases (ownSlice_split_all n p _ _ ⟨by omega, by omega⟩).1 $$ Hp with ⟨Hp1, Hp2⟩
      have Htk : (ys ++ xs.drop ys.length).take (sint.nat n) = ys := by
        rw [show sint.nat n = ys.length by word, List.take_left]
      have Hdr : (ys ++ xs.drop ys.length).drop (sint.nat n) = xs.drop ys.length := by
        rw [show sint.nat n = ys.length by word, List.drop_left]
      rw [Htk, Hdr]
      wp_auto
      wp_apply io.wp_reader_Read ri Pre S E (r0 ++ ys) _ (xs.drop ys.length)
          (by rw [List.length_drop]; exact Hpre ys ⟨by omega, by omega⟩) $$ [Hp2 HS]
        as %nn %err' ⟨%zs, %Hzs, Hp2, HS, #Herr', %Hty'⟩
      · iframe Hr HS Hp2
      wp_for_post
      iframe
      iexists _, _, ys ++ zs
      rw [show r0 ++ (ys ++ zs) = r0 ++ ys ++ zs from (List.append_assoc _ _ _).symm]
      iframe
      iframe Herr'
      have Hzl : zs.length ≤ xs.length - ys.length := by
        rw [List.length_drop] at Hzs; exact Hzs.2
      isplitl [Hp1 Hp2]
      · have e := ownSlice_combine (GF := GF) (V := w8) n p (DFrac.own 1) ys (zs ++ (xs.drop ys.length).drop zs.length)
          (W64 0) p.len ⟨by word, by decide, by word, by word⟩
        rw [List.length_append, ← List.drop_drop]
        rw [← List.append_assoc] at e
        iapply ownSlice_trivial_slice_2
        iapply e $$ Hp1 Hp2
      ipureintro
      simp only [List.length_append]
      refine ⟨Hty', ?_, ?_⟩
      · have h2 : (xs.length : Int) = sint.Z p.len := by
          have h := Hlen.1; have h' := Hlen.2; rw [h]; word
        have : (ys.length + zs.length : Int) < 2 ^ 63 := by
          have : sint.Z p.len < 2 ^ 63 := by word
          omega
        word
      · omega
    · -- `err != nil`: the loop ends
      wp_auto
      simp only [decide_eq_true_eq, ↓reduceIte]
      rw [ite_eq_right (by intro h; have := go.intoVal_inj h; simp at this)]
      try wp_auto
      wp_if_destruct
      · exfalso; word
      wp_if_destruct
      · -- `n > 0`: compare `err` with `EOF`
        try wp_auto
        by_cases hty : ei.ty = go.GoType.PointerType errors.errorString.ty
        · obtain ⟨l, hl⟩ := Hty ei _ rfl hty
          obtain ⟨ty, v⟩ := ei
          simp only at hty hl
          subst hty hl
          simp only [interface.mkOk, ↓reduceIte]
          wp_auto
          wp_if_destruct
          · iapply HΦ
            iexists ys
            iframe Hp HS
            isplit
            · ipureintro; exact Hys
            unfold io.readAtLeastRes io.errAt
            icases Herr with (%Hnil | #HE)
            · exfalso; cases Hnil
            iright; iright
            iexists (GoInterface.ok ⟨_, #l⟩)
            iframe HE
            ipureintro
            have hne : ys ≠ [] := by
              intro h; subst h; simp at Hys; word
            refine ⟨Hmin, by word, by simp, fun _ => rfl, fun h => absurd ⟨?_, hne⟩ h⟩
            simp only [Hif]
          · iapply HΦ
            iexists ys
            iframe Hp HS
            isplit
            · ipureintro; exact Hys
            unfold io.readAtLeastRes io.errAt
            icases Herr with (%Hnil | #HE)
            · exfalso; cases Hnil
            iright; iright
            iexists (GoInterface.ok ⟨_, #l⟩)
            iframe HE
            ipureintro
            refine ⟨Hmin, by word, by simp, fun h => absurd ?_ Hif, fun _ => rfl⟩
            obtain ⟨h1, -⟩ := h
            simp only [GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h1
            exact go.intoVal_inj h1.2
        · simp only [interface.mkOk, hty, ↓reduceIte]
          wp_auto
          iapply HΦ
          iexists ys
          iframe Hp HS
          isplit
          · ipureintro; exact Hys
          unfold io.readAtLeastRes io.errAt
          icases Herr with (%Hnil | #HE)
          · exfalso; cases Hnil
          iright; iright
          iexists (GoInterface.ok ei)
          iframe HE
          ipureintro
          refine ⟨Hmin, by word, by simp, fun h => absurd ?_ hty, fun _ => rfl⟩
          obtain ⟨h1, -⟩ := h
          simp only [GoInterface.ok.injEq] at h1
          rw [h1]
      · -- `n == 0`
        iapply HΦ
        iexists ys
        iframe Hp HS
        isplit
        · ipureintro; exact Hys
        unfold io.readAtLeastRes io.errAt
        icases Herr with (%Hnil | #HE)
        · exfalso; cases Hnil
        iright; iright
        iexists (GoInterface.ok ei)
        iframe HE
        ipureintro
        have hnil : ys = [] := by
          apply List.eq_nil_of_length_eq_zero; word
        refine ⟨Hmin, by word, by simp, fun h => absurd hnil h.2, fun _ => rfl⟩
  · -- `n >= min`: `nil`
    try simp only [decide_eq_true_eq, ↓reduceIte]
    try wp_auto
    wp_if_destruct
    · iapply HΦ
      iexists ys
      iframe Hp HS
      isplit
      · ipureintro; exact Hys
      unfold io.readAtLeastRes
      iright; ileft
      ipureintro
      exact ⟨Hmin, by word, rfl⟩
    · exfalso; word

theorem wp_ReadFull_lt :
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r0 : List w8) (p : GoSlice) (xs : List w8)
    (eof ueof : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ io.readerOk ri Pre S E ∗
      globalAddr io.EOF ↦□ eof ∗ globalAddr io.ErrUnexpectedEOF ↦□ ueof ∗
      ⌜∀ ys : List w8, ys.length < xs.length → Pre (r0 ++ ys) (xs.length - ys.length)⌝ ∗
      S r0 ∗ p ↦* xs }}
    (App (App (Val (@! io.ReadFull)) (Val #(interface.ok ri))) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ S (r0 ++ ys) ∗
        io.readFullRes E eof ueof r0 ys xs.length err }} := by
  intro ri Pre S E r0 p xs eof ueof
  wp_start as ⟨#Hr, #Heof, #Hueof, %Hpre, HS, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hp
  ihave Hi := io.isInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, HSB, -⟩
  iunfold errors.newVar at HSB
  icases HSB with ⟨%xsb, #HSB, -⟩
  wp_auto
  wp_apply wp_ReadAtLeast_lt ri Pre S E r0 p xs p.len eof ueof _ $$ [Hp HS]
    as %n %err ⟨%ys, %Hys, Hp, HS, #Hres⟩
  · iframe Hr Heof Hueof HSB HS Hp
    ipureintro
    intro ys hys
    exact Hpre ys hys.2
  wp_auto
  iapply HΦ
  iexists ys
  iframe Hp HS
  isplit
  · ipureintro; exact Hys
  have hm : sint.Z p.len = ((xs.length : Nat) : Int) := by word
  rw [hm]
  iapply io.readFullRes_of_readAtLeastRes E eof ueof _ r0 ys xs.length err Hys.2 $$ Hres

end io

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]

/-- The configuration addresses' protocol, both ways: trivial (the bytes mean nothing; a machine
trusts only what `decode` checks). -/
def confProto : Proto GF := fun _ _ => iprop(True)

/-- A message `awaitConf` sends on its channel: an accepted configuration and its removals, the
slice owned (fresh from `decode`). -/
def msgOk (m : msg) : IProp GF :=
  iprop(⌜confOk m.conf'⌝ ∗ ∃ rs : List removal, m.rs' ↦* rs ∗ ⌜remsOk m.conf' rs⌝)

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]
variable [field_sem : net.FieldAssumptions]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

set_option goose.wp.extras true

/-- `rnd(n)` of `n ≠ 0`: a number below `n`. -/
theorem wp_rnd (n : w64) (hn : n ≠ W64 0) :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.rnd)) (Val #n))
    {{ (r : w64), RET #r; ⌜uint.Z r < uint.Z n⌝ }} := by
  wp_start
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x _
  have h0 : ¬ uint.Z n = 0 := by intro h; apply hn; word
  simp only [h0, ↓reduceIte]
  wp_auto
  iapply HΦ
  ipureintro
  have hlt : x % n < n := BitVec.umod_lt x (by word)
  word

/-- `choose()`: a configuration `decode` accepts. -/
theorem wp_choose :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.choose)) (Val #()))
    {{ (conf : Conf), RET #conf; ⌜confOk conf⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_rnd (W64 3) (by decide) as %a %Ha
  wp_apply wp_rnd (W64 3) (by decide) as %b %Hb
  wp_apply wp_rnd (W64 2) (by decide) as %c %Hc
  iapply HΦ
  ipureintro
  unfold confOk
  simp only
  refine ⟨by word, by word, by word, by word⟩

/-- `plan(conf)` of an accepted `conf`: one or two removals, `planOk`. -/
theorem wp_plan (conf : Conf) (hok : confOk conf) :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.plan)) (Val #conf))
    {{ (rs : GoSlice), RET #rs; ∃ rl : List removal, rs ↦* rl ∗ ⌜planOk conf rl⌝ }} := by
  wp_start
  wp_auto
  wp_apply wp_rnd (W64 2) (by decide) as %n %Hn
  ihave HI : (∃ (j : w64) (rsl : GoSlice) (l : List removal),
      "i" ∷ i_ptr ↦ j ∗ "rs" ∷ rs_ptr ↦ rsl ∗ "Hrs" ∷ rsl ↦* l ∗
      "Hcap" ∷ ownSliceCap removal rsl (DFrac.own 1) ∗
      "%Hinv" ∷ ⌜l.length = uint.nat j ∧ uint.Z j ≤ uint.Z (W64 1 + n) ∧
        ∀ r ∈ l, uint.Z r.Client' < 5 ∧ remOk conf r⌝ : IProp GF) $$ [i rs]
  · iexists W64 0, slice.nil, []
    iframe i rs
    isplitr; · iapply ownSlice_nil
    isplitr; · iapply ownSliceCap_nil
    ipureintro; simp only [List.length_nil, List.not_mem_nil, false_implies, implies_true,
      and_true]; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have hN : conf.N' ≠ W64 0 := by intro h; unfold confOk at hok; rw [h] at hok; word
    wp_apply wp_rnd (W64 5) (by decide) as %rc %Hrc
    wp_apply wp_rnd conf.N' hN as %rn %Hrn
    wp_apply wp_rnd (W64 6 - W64 1) (by decide) as %ra %Hra
    wp_apply wp_slice_literal (V := removal)
      (l := [({ Client' := rc, Node' := W64 2 + rn, After' := W64 1 + ra } : removal)])
    isplitr
    · ipureintro; rfl
    iintro %kp ⟨Htmp, -⟩
    wp_auto
    wp_apply wp_slice_append (V := removal) $$ [$Hrs $Hcap $Htmp] as %rsl' ⟨Hrs, Hcap, -⟩
    wp_for_post
    iframe
    iexists j + W64 1, rsl', _
    iframe
    ipureintro
    have hj : uint.Z j < uint.Z (W64 1 + n) := Hif
    refine ⟨by simp only [List.length_append, List.length_singleton, Hinv.1]; word, by word, ?_⟩
    intro r hr
    rcases List.mem_append.1 hr with h | h
    · exact Hinv.2.2 r h
    · simp only [List.mem_singleton] at h; subst h
      unfold confOk at hok; unfold remOk; simp only
      refine ⟨by word, by word, by word, by word, by word⟩
  · iapply HΦ
    iexists l
    iframe Hrs
    ipureintro
    have hj : ¬ uint.Z j < uint.Z (W64 1 + n) := Hif
    refine ⟨by rw [Hinv.1]; word, by rw [Hinv.1]; word, Hinv.2.2⟩

/-- `mine(rs, c)`: a slice of some of `rs`'s removals, in order (a sublist). -/
theorem wp_mine (rs : GoSlice) (rl : List removal) (dq : DFrac) (c : w64) :
    {{ (rs ↦*{dq} rl : IProp GF) }}
      (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.mine)) (Val #rs)) (Val #c))
    {{ (m : GoSlice), RET #m; ∃ ml : List removal, m ↦* ml ∗ ⌜ml.Sublist rl⌝ ∗
        rs ↦*{dq} rl }} := by
  wp_start as Hrs
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hrs
  ihave HI : (∃ (j : w64) (rv : removal) (ms : GoSlice) (ml : List removal),
      "i" ∷ i_ptr ↦ j ∗ "r" ∷ r_ptr ↦ rv ∗ "m" ∷ m_ptr ↦ ms ∗
      "Hms" ∷ ms ↦* ml ∗ "Hmc" ∷ ownSliceCap removal ms (DFrac.own 1) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z rs.len ∧ ml.Sublist (rl.take (sint.nat j))⌝ : IProp GF)
      $$ [i r m]
  · iexists W64 0, _, slice.nil, []
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; refine ⟨by word, by word, List.nil_sublist _⟩
  wp_for HI
  wp_if_destruct
  · simp only [Hj.1, Hif, _root_.and_self, ↓reduceIte]
    list_elem rl (sint.nat j) as e
    wp_apply wp_load_slice_index rs (sint.Z j) rl _ e Hj.1 $$ [Hrs] with Hrs
    · iframe; ipureintro; exact He_lookup
    (try wp_auto)
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have htk : rl.take (sint.nat (j + W64 1)) = rl.take (sint.nat j) ++ [e] := by
      rw [hj1, List.take_add_one, He_lookup]; rfl
    wp_if_destruct
    · wp_apply wp_slice_literal (l := [e])
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Htmp, -⟩
      wp_auto
      wp_apply wp_slice_append (V := removal) $$ [$Hms $Hmc $Htmp]
        as %ms' ⟨Hms, Hmc, -⟩
      wp_for_post
      iframe
      iexists j + W64 1, e, ms', ml ++ [e]
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htk]; exact Hj.2.2.append (List.Sublist.refl _)
    · wp_for_post
      iframe
      iexists j + W64 1, e, ms, ml
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htk]; exact Hj.2.2.trans (List.sublist_append_left _ _)
  · (try wp_auto)
    iapply HΦ
    iexists ml
    iframe
    ipureintro
    have hjl : sint.nat j = rl.length := by rw [Hlen.1]; word
    rw [hjl, List.take_length] at Hj
    exact Hj.2.2

/-- `c.String()`: a string. -/
theorem wp_Conf_String (conf : Conf) :
    {{ (True : IProp GF) }}
      (App (Val #(methods Conf.ty go!"String" #conf)) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  wp_start
  wp_auto
  wp_pures
  iStructNamed c
  wp_if_destruct
  · wp_apply wp_digit
    wp_apply wp_digit
    wp_apply wp_digit
    iapply HΦ; itrivial
  · wp_apply wp_digit
    wp_apply wp_digit
    iapply HΦ; itrivial

set_option hygiene false in
/-- A store into the message's slice `b` (8 bytes) at an index below 8. -/
local macro "bstore" : tactic => `(tactic| (
  (try wp_auto)
  rw [ite_eq_left (by constructor <;> word)]
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] as Hb
  · iframe; ipureintro; (try simp only [List.length_set, List.length_replicate]); word))

/-- `c.encode(rs)`, for at most two removals: an eight-byte message. -/
theorem wp_Conf_encode (conf : Conf) (rs : GoSlice) (rl : List removal) (dq : DFrac)
    (hl : rl.length ≤ 2) :
    {{ (rs ↦*{dq} rl : IProp GF) }}
      (App (Val #(methods Conf.ty go!"encode" #conf)) (Val #rs))
    {{ (b : GoSlice), RET #b; ∃ bs : List w8, b ↦* bs ∗ ⌜bs.length = 8⌝ ∗ rs ↦*{dq} rl }} := by
  wp_start as Hrs
  wp_auto
  wp_pures
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %b ⟨Hb, -⟩
  · ipureintro; word
  iStructNamed c
  irename: (("_" ∷ True : IProp GF)) => Hjunk
  iclear Hjunk
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  simp only [List.length_replicate] at Hbl
  bstore
  bstore
  bstore
  bstore
  have hbsl : (((((List.replicate 8 (zero_val w8)).set 0 (W8 (uint.Z conf.N'))).set 1
    (W8 (uint.Z conf.Late'))).set 2 (W8 (uint.Z conf.ReadTail'))).set 3
    (W8 (sint.Z rs.len))).length = 8 := by simp
  generalize (((((List.replicate 8 (zero_val w8)).set 0 (W8 (uint.Z conf.N'))).set 1
    (W8 (uint.Z conf.Late'))).set 2 (W8 (uint.Z conf.ReadTail'))).set 3 (W8 (sint.Z rs.len))) = bs
    at hbsl ⊢
  wp_auto
  rename_i ki_ptr
  irename: (ki_ptr ↦ (zero_val w64) : IProp GF) => ki
  ihave %Hlen := ownSlice_len _ _ _ $$ Hrs
  ihave HI : (∃ (j kv : w64) (rv : removal) (bs : List w8),
      "i" ∷ i_ptr ↦ j ∗ "ki" ∷ ki_ptr ↦ kv ∗ "r" ∷ r_ptr ↦ rv ∗ "Hb" ∷ b ↦* bs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z rs.len ∧ bs.length = 8⌝ : IProp GF)
      $$ [i ki r Hb]
  · iexists W64 0, _, _, bs
    iframe
    ipureintro; exact ⟨by word, by word, hbsl⟩
  wp_for HI
  wp_if_destruct
  · simp only [Hj.1, Hif, _root_.and_self, ↓reduceIte]
    list_elem rl (sint.nat j) as e
    wp_apply wp_load_slice_index rs (sint.Z j) rl _ e Hj.1 $$ [Hrs] with Hrs
    · iframe; ipureintro; exact He_lookup
    have hjl : sint.nat j < 2 := by rw [Hlen.1] at hl; word
    bstore
    bstore
    wp_for_post
    iframe
    iexists j + W64 1, j, e, _
    iframe
    ipureintro; simp only [List.length_set]; exact ⟨by word, by word, Hj.2.2⟩
  · (try wp_auto)
    iapply HΦ
    iexists bs
    iframe
    ipureintro; exact Hj.2.2

/-- `c.String()` through a pointer. -/
theorem wp_Conf_String_ptr (l : Loc) (conf : Conf) (dq : DFrac) :
    {{ (l ↦{dq} conf : IProp GF) }}
      (App (Val #(methods (go.GoType.PointerType Conf.ty) go!"String" #l)) (Val #()))
    {{ (s : GoString), RET #s; l ↦{dq} conf }} := by
  wp_start as Hl
  wp_auto
  wp_apply wp_Conf_String conf as %s -
  iapply HΦ $$ Hl

/-- `c.encode(rs)` through a pointer. -/
theorem wp_Conf_encode_ptr (l : Loc) (conf : Conf) (dq' : DFrac) (rs : GoSlice)
    (rl : List removal) (dq : DFrac) (hl : rl.length ≤ 2) :
    {{ (l ↦{dq'} conf ∗ rs ↦*{dq} rl : IProp GF) }}
      (App (Val #(methods (go.GoType.PointerType Conf.ty) go!"encode" #l)) (Val #rs))
    {{ (b : GoSlice), RET #b; ∃ bs : List w8, b ↦* bs ∗ ⌜bs.length = 8⌝ ∗ l ↦{dq'} conf ∗
        rs ↦*{dq} rl }} := by
  wp_start as ⟨Hl, Hrs⟩
  wp_auto
  wp_apply wp_Conf_encode conf rs rl dq hl $$ [$Hrs] as %b ⟨%bs, Hb, %Hbl, Hrs⟩
  iapply HΦ
  iexists bs
  iframe
  ipureintro; exact Hbl

/-- A byte's load, curried (for the macro below). -/
theorem wp_ld_byte (b : GoSlice) (vs : List w8) (dq : DFrac) (i : Int) (v : w8) (hi : 0 ≤ i)
    (hv : vs[i.toNat]? = some v) (Φ : val → IProp GF) :
    ⊢ b ↦*{dq} vs -∗ ▷ (b ↦*{dq} vs -∗ Φ #v) -∗
      WP (App (Val (GoInstruction (GoLoad go.byte))) (Val #(sliceIndexRef w8 i b))) {{ Φ }} := by
  iintro Hb HΦ
  wp_apply wp_load_slice_index b i vs dq v hi $$ [$Hb] as Hb
  · ipureintro; exact hv
  iapply HΦ $$ Hb

set_option hygiene false in
/-- Load byte `v` of `b` (at a literal index). -/
local macro "ld_byte" v:term : tactic => `(tactic| (
  rw [hbl, ite_eq_left (by decide)]
  wp_apply wp_ld_byte _ _ _ _ $v (by decide) (by rfl) $$ Hb as Hb))

set_option hygiene false in
/-- `decode`'s refusal. -/
local macro "dec_fail" : tactic => `(tactic| (
  iapply HΦ; iframe Hb; ileft; ipureintro; rfl))

set_option hygiene false in
/-- `decode`'s loop body for removal `iv`, its bytes `bA`, `bB`. -/
local macro "dec_body" iv:term:max bA:term:max bB:term:max : tactic => `(tactic| (
  ld_byte $bA
  ld_byte $bB
  wp_if_destruct
  · wp_for_post
    dec_fail
  wp_if_destruct
  · wp_for_post
    dec_fail
  wp_if_destruct
  · wp_for_post
    dec_fail
  wp_if_destruct
  · wp_for_post
    dec_fail
  wp_apply wp_slice_literal
    (l := [({ Client' := W64 0, Node' := W64 (uint.Z $bA), After' := W64 (uint.Z $bB) } :
      removal)])
  isplitr
  · ipureintro; rfl
  iintro %kp1 ⟨Htmp, -⟩
  wp_auto
  wp_apply wp_slice_append (V := removal) $$ [Hrs Hcap Htmp]
    as %rsl' ⟨Hrs, Hcap, -⟩
  · iframe Hrs Hcap Htmp
  wp_for_post
  iframe
  iexists $iv + W64 1, rsl', _
  iframe
  ipureintro
  refine ⟨by simp only [List.length_append, List.length_singleton, Hinv.1]; word, by word, ?_⟩
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · exact Hinv.2.2 r h
  · simp only [List.mem_singleton] at h; subst h
    unfold confOk at hok; unfold remOk; simp only; word))


/-- `decode(b)` of eight bytes: `ok` only for a message whose configuration and removals meet
`msgOk`. -/
theorem wp_decode (b : GoSlice) (bs : List w8) (dq : DFrac) (hlen : bs.length = 8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (Val (@! github_com.despreston.go_craq.examples.craqnet.decode)) (Val #b))
    {{ (conf : Conf) (rs : GoSlice) (ok : Bool), RET (PairV (PairV #conf #rs) #ok);
        b ↦*{dq} bs ∗ (⌜ok = false⌝ ∨ msgOk { conf' := conf, rs' := rs }) }} := by
  wp_start as Hb
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  have hbl : sint.Z b.len = 8 := by have := Hl.1; rw [hlen] at this; word
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ :
      ∃ b0 b1 b2 b3 b4 b5 b6 b7, bs = [b0, b1, b2, b3, b4, b5, b6, b7] := by
    match bs, hlen with
    | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  wp_auto
  ld_byte b0
  ld_byte b1
  ld_byte b2
  wp_if_destruct
  · dec_fail
  wp_if_destruct
  · dec_fail
  wp_if_destruct
  · dec_fail
  wp_if_destruct
  · dec_fail
  ld_byte b3
  wp_if_destruct
  · dec_fail
  have hok : confOk { N' := W64 (uint.Z b0), Late' := W64 (uint.Z b1), ReadTail' := W64 (uint.Z b2) } := by
    unfold confOk; simp only at *; word
  generalize hcf : ({ N' := W64 (uint.Z b0), Late' := W64 (uint.Z b1), ReadTail' := W64 (uint.Z b2) } :
    Conf) = cf at *
  ihave HI : (∃ (iv : w64) (rsl : GoSlice) (l : List removal),
      "i" ∷ i_ptr ↦ iv ∗ "rs" ∷ rs_ptr ↦ rsl ∗ "Hrs" ∷ rsl ↦* l ∗
      "Hcap" ∷ ownSliceCap removal rsl (DFrac.own 1) ∗
      "%Hinv" ∷ ⌜l.length = uint.nat iv ∧ uint.nat iv ≤ uint.nat b3 ∧ ∀ r ∈ l, remOk cf r⌝ : IProp GF)
    $$ [i rs]
  · iexists W64 0, slice.nil, []
    iframe i rs
    isplitr; · iapply ownSlice_nil
    isplitr; · iapply ownSliceCap_nil
    ipureintro; simp
  wp_for HI
  ld_byte b3
  cleanup_bool_decide
  wp_if_destruct
  · have hiv : iv = W64 0 ∨ iv = W64 1 := by word
    rcases hiv with rfl | rfl
    · dec_body (W64 0) b4 b5
    · dec_body (W64 1) b6 b7
  iapply HΦ
  iframe Hb
  iright
  unfold msgOk
  isplitr
  · ipureintro; exact hok
  iexists l
  iframe Hrs
  ipureintro
  exact ⟨by rw [Hinv.1]; word, Hinv.2.2⟩

end proof

/-! ### The network: `sendConf`, `configure`, `awaitConf` -/

section net
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

set_option goose.wp.extras true

/-- The package facts the network code reads, from the kit's initialization (through remote's,
`remote.eof_init`, `remote.ed_init`, and `io`'s): `io`'s initialization, `io.EOF`'s,
`io.ErrUnexpectedEOF`'s and `poll.ErrDeadlineExceeded`'s values. -/
theorem kit_net_init :
    isPkgInit (PROP := IProp GF) kpkg ⊢
      isPkgInit (PROP := IProp GF) pkg_id.io ∗
      (∃ eof : GoInterface, globalAddr io.EOF ↦□ eof) ∗
      (∃ ueof : GoInterface, globalAddr io.ErrUnexpectedEOF ↦□ ueof) ∗
      (∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed) := by
  iintro #Hpkg
  ihave #Hrem : (isPkgInit (PROP := IProp GF)
    pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote) $$ []
  · iPkgInit
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Heof := github_com.mit_pdos.etcd_grove.examples.lib.remote.eof_init $$ Hrem
  ihave #Hed := github_com.mit_pdos.etcd_grove.examples.lib.remote.ed_init $$ Hrem
  ihave #Hi := io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, -, HU, -⟩
  iunfold errors.newVar at HU
  icases HU with ⟨%xu, #HU, -⟩
  iframe Hio Heof Hed
  iexists _
  iexact HU

/-- The update `net.Conn.Close.spec` takes, with `Q _ := True` (`close_au`). -/
theorem close_upd (cn : Nat) (s : Bool) :
    connIs (Gg := hG.goose_globalGS) cn ⊢
      |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
        netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d ∗
        ∀ res st' d', ⌜CloseOutcome st d res st' d'⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st' -∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ (True : IProp GF) := by
  iintro #Hconn
  imod close_au cn s $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
  imodintro
  iexists st, dd
  iframe Hst Hdd
  iintro %res %st' %d' %Hd Hst Hdd
  imod Hcl $$ %res %st' %d' %Hd Hst Hdd with -
  imodintro
  itrivial

set_option hygiene false in
/-- `sendConf`'s end: the `Close`, then the result. -/
local macro "send_close" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply wp_Close t cn false a la ra (fun _ => iprop(True)) $$ [] as %e2 -
  · iframe Hca
    iapply close_upd cn false $$ Hconn
  (try wp_auto)
  iapply HΦ; iexact Hb))

/-- `sendConf(addr, b)`: to an address with the configuration protocol, some answer. -/
theorem wp_sendConf
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (a : GoString) (b : GoSlice) (bs : List w8) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗
        addrProto (Gg := hG.goose_globalGS) a confProto confProto ∗ b ↦*{dq} bs }}
      (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.sendConf)) (Val #a))
        (Val #b))
    {{ (ok : Bool), RET #ok; b ↦*{dq} bs }} := by
  wp_start as ⟨#Ha, Hb⟩
  ihave ⟨#Hio, ⟨%eof, #Heof⟩, ⟨%ueof, #Hueof⟩, ⟨%ed, #Hed⟩⟩ := kit_net_init $$ Hpkg
  ihave %Hok := addrTok_ok a $$ [Ha]
  · iapply addrProto_tok $$ Ha
  wp_auto
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp a iprop(True)
      (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false confProto confProto [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn false)) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, ⟨Hend, -⟩⟩ | ⟨-, %x, -, #Herr⟩)
  · isplitr
    · ipureintro; exact Hok
    isplit
    · itrivial
    · iapply dial_au a confProto confProto $$ Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    wp_auto
    unfold connEnd
    icases Hend with ⟨Hsend, Hrecv⟩
    ihave #Hconn := sendTok_connIs cn false confProto [] $$ Hsend
    ihave #HP : (□ confProto (GF := GF) cn ([] ++ bs) : IProp GF) $$ []
    · iintro !>; unfold confProto; itrivial
    wp_apply wp_Write t cn false a la ra b bs dq ed (writeP cn false confProto []) $$ [Hb Hsend]
      as %n %err ⟨%w, %res, Hs, Hb, %Hw, #HE⟩
    · iframe Hca Hb Hed
      isplitl [Hsend]
      · iapply writeP_init $$ Hsend
      · iapply write_acc cn false confProto [] bs $$ HP
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    rcases err with ei | _
    · send_close
    wp_auto
    ihave #Hrd := net.conn_readerOk wp_Read t cn false a la ra eof ed confProto $$ [$Hio $Hca $Heof $Hed]
    ihave Hsl := slice_array a_ptr 1 _ (by decide) $$ a
    simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
      show (W64 1 - W64 0) = W64 1 from rfl]
    ihave HrL := recvTok_L cn false confProto [] $$ Hrecv
    rw [show interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t =
      GoInterface.ok (net.connIface t) from rfl]
    wp_apply wp_ReadFull_lt (net.connIface t) _ _ _ [] _ _ eof ueof $$ [$Hrd $Hio $Heof $Hueof $HrL $Hsl]
      as %n2 %err2 ⟨%ys, %Hys, Hsl, HrL, #Hres⟩
    · ipureintro; intro ys hys; omega
    rcases err2 with ei | _
    · wp_auto
      send_close
    have hl1 : (ys ++ List.drop ys.length (List.replicate 1 (zero_val w8))).length = 1 := by
      have := Hys.2
      have h1 : (zero_val (GoArray w8 1)).arr.length = 1 := rfl
      simp only [List.length_append, List.length_drop, List.length_replicate]; omega
    obtain ⟨v, hv⟩ : ∃ v, (ys ++ List.drop ys.length (List.replicate 1 (zero_val w8)))[0]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_auto
    rw [show arrayIndexRef w8 (sint.Z (W64 0)) a_ptr =
      sliceIndexRef w8 (sint.Z (W64 0)) (slice.mk a_ptr (W64 1) (W64 1)) from rfl]
    wp_apply wp_load_slice_index _ _ _ _ v (by decide) $$ [$Hsl] as Hsl
    · ipureintro; exact hv
    wp_if_destruct <;> send_close
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ
    iexact Hb

theorem confAddrs_proto (i : Nat) (a : GoString) (h : confAddrs[i]? = some a) :
    ([∗list] x ∈ confAddrs, addrProto (Gg := hG.goose_globalGS) x confProto confProto) ⊢
      addrProto (Gg := hG.goose_globalGS) a confProto confProto := by
  iintro H
  iapply BigSepL.bigSepL_lookup h $$ H

/-- `configure(conf, rs)` of an accepted configuration and at most two removals: every client
machine's configuration address and chain machine `2..N+1`'s, each until acknowledged. -/
theorem wp_configure [LogHyp GF]
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (conf : Conf) (rs : GoSlice) (rl : List removal) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ rs ↦*{dq} rl ∗ ⌜confOk conf ∧ rl.length ≤ 2⌝ ∗
        [∗list] a ∈ confAddrs, addrProto (Gg := hG.goose_globalGS) a confProto confProto }}
      (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.configure)) (Val #conf))
        (Val #rs))
    {{ RET #(); rs ↦*{dq} rl }} := by
  wp_start as ⟨Hrs, %Hok, #Hpr⟩
  ihave #Hlog : (isPkgInit (PROP := IProp GF) pkg_id.log) $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Conf_String_ptr conf_ptr conf _ $$ [$conf] as %s1 conf
  wp_apply wp_digit
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType [])
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %args_sl ⟨Hargs, -⟩
  wp_apply LogHyp.wp_Println _ _ _ $$ [Hargs]
  · iframe
    iapply argOks_of_wf _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)
  iintro -
  wp_auto
  wp_apply wp_ConfAddrs as %cfgs Hcfgs
  ihave %Hcl := ownSlice_len _ _ _ $$ Hcfgs
  have hcl : sint.Z cfgs.len = 11 := by
    have := Hcl.1; simp only [confAddrs, List.length_cons, List.length_nil] at this; word
  ihave HI : (∃ c : w64, "c" ∷ c_ptr ↦ c ∗ "%Hc" ∷ ⌜uint.Z c ≤ 5⌝ : IProp GF) $$ [c]
  · iexists W64 0; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · have hc5 : uint.Z c < 5 := Hif
    have hcn : sint.nat c < confAddrs.length := by
      simp only [confAddrs, List.length_cons, List.length_nil]; word
    list_elem confAddrs (sint.nat c) as a
    wp_for
    rw [ite_eq_left ⟨by word, by word⟩]
    wp_apply wp_load_slice_index cfgs (sint.Z c) confAddrs _ a (by word) $$ [Hcfgs] with Hcfgs
    · iframe; ipureintro; exact Ha_lookup
    wp_apply wp_mine rs rl dq c $$ [$Hrs] as %m ⟨%ml, Hm, %Hml, Hrs⟩
    wp_apply wp_Conf_encode_ptr conf_ptr conf _ m ml _ (by have := Hml.length_le; omega)
      $$ [$conf $Hm] as %b ⟨%bs, Hb, -, conf, -⟩
    ihave #Hp := confAddrs_proto _ _ Ha_lookup $$ Hpr
    wp_apply wp_sendConf wp_Dial wp_Write wp_Read wp_Close a b bs _ $$ [$Hpkg $Hp $Hb] as %ok -
    cases ok
    · simp only [Bool.not_false, decide_true, ↓reduceIte]
      wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
    · simp only [Bool.not_true]
      cleanup_bool_decide
      wp_for_post
      iframe
      iexists c + W64 1
      iframe
      ipureintro; word
  (try wp_auto)
  have hN := Hok.1
  unfold confOk at hN
  ihave HK : (∃ k : w64, "k" ∷ k_ptr ↦ k ∗
      "%Hk" ∷ ⌜2 ≤ uint.Z k ∧ uint.Z k ≤ uint.Z conf.N' + 2⌝ : IProp GF) $$ [k]
  · iexists W64 2; iframe; ipureintro; word
  wp_for HK
  wp_if_destruct
  · have hNw : uint.Z (conf.N' + W64 1) = uint.Z conf.N' + 1 := by word
    have hk : uint.Z k ≤ uint.Z conf.N' + 1 := by rw [← hNw]; exact Hif
    have hidx : sint.Z (W64 5 + k - W64 1) = 4 + uint.Z k := by word
    have hkn : sint.nat (W64 5 + k - W64 1) < confAddrs.length := by
      simp only [confAddrs, List.length_cons, List.length_nil]; word
    list_elem confAddrs (sint.nat (W64 5 + k - W64 1)) as a
    wp_for
    rw [ite_eq_left ⟨by word, by word⟩]
    wp_apply wp_load_slice_index cfgs _ confAddrs _ a (by word) $$ [Hcfgs] with Hcfgs
    · iframe; ipureintro; exact Ha_lookup
    ihave Hnil := ownSlice_nil (V := removal) (GF := GF) (DFrac.own 1)
    wp_apply wp_Conf_encode_ptr conf_ptr conf _ slice.nil [] _ (by simp) $$ [$conf $Hnil]
      as %b ⟨%bs, Hb, -, conf, -⟩
    ihave #Hp := confAddrs_proto _ _ Ha_lookup $$ Hpr
    wp_apply wp_sendConf wp_Dial wp_Write wp_Read wp_Close a b bs _ $$ [$Hpkg $Hp $Hb] as %ok -
    cases ok
    · simp only [Bool.not_false, decide_true, ↓reduceIte]
      wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
    · simp only [Bool.not_true]
      cleanup_bool_decide
      wp_for_post
      iframe
      iexists k + W64 1
      iframe
      ipureintro; word
  · (try wp_auto)
    iapply HΦ $$ Hrs

set_option hygiene false in
/-- The end of an `awaitConf` iteration: the connection closed, the loop's invariant kept. -/
local macro "await_close" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %e2 -
  · iframe Hca
    iapply close_upd cn true $$ Hconn
  (try wp_auto)
  wp_for_post
  iframe
  iexists _; iframe))

set_option hygiene false in
/-- The acknowledgment, then the end of the iteration. -/
local macro "await_ack" : tactic => `(tactic| (
  wp_apply wp_slice_literal (l := [W8 107])
  isplitr
  · ipureintro; rfl
  iintro %kp ⟨Hk, -⟩
  wp_auto
  wp_apply wp_Write tc cn true a la ra _ [W8 107] _ ed (writeP cn true confProto []) $$ [Hk Hsend]
    as %nw %errw ⟨%w, %resw, Hs, Hk, -, -⟩
  · iframe Hca Hk Hed
    isplitl [Hsend]
    · iapply writeP_init $$ Hsend
    · iapply write_acc cn true confProto [] [W8 107] $$ HP
  await_close))

/-- `awaitConf(addr, ch)` (at a client machine or a chain machine, `addr` its configuration
address, with the configuration protocol): from a bag channel of `msgOk` messages, it sends only
`msgOk` messages; it never returns. -/
theorem wp_awaitConf
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (a : GoString) (γch : ChanNames) (ch : Loc) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗
        addrProto (Gg := hG.goose_globalGS) a confProto confProto ∗
        isChanBag γch ch (V := msg) (msgOk (hG := hG)) }}
      (App (App (Val (@! github_com.despreston.go_craq.examples.craqnet.awaitConf)) (Val #a))
        (Val #ch))
    {{ RET #(); False }} := by
  wp_start as ⟨#Ha, #Hbag⟩
  ihave ⟨#Hio, ⟨%eof, #Heof⟩, ⟨%ueof, #Hueof⟩, ⟨%ed, #Hed⟩⟩ := kit_net_init $$ Hpkg
  ihave %Hok := addrTok_ok a $$ [Ha]
  · iapply addrProto_tok $$ Ha
  wp_auto
  wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp a as %li %err HL
  · iframe %Hok
    iapply listen_au $$ Ha
  ihave HI : (∃ (li : GoInterface) (err : GoInterface), "l" ∷ l_ptr ↦ li ∗ "err" ∷ err_ptr ↦ err ∗
      "HL" ∷ ((⌜err = GoInterface.nil⌝ ∗ ∃ l, net.isListener li l ∗
          netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
          netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a) ∨
        ∃ pe : Loc, ⌜err = interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe⌝) : IProp GF)
      $$ [l err HL]
  · iexists li, err
    iframe l err
    icases HL with (⟨%He, Hl⟩ | ⟨%x, -, #HE⟩)
    · ileft
      iframe Hl
      ipureintro; exact He
    · iright
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      iexists pe
      ipureintro; rfl
  wp_for HI
  icases HL with (⟨%He, %l, #Hli, Hlis, #Hla⟩ | ⟨%pe, %He⟩)
  rotate_left
  · -- a failure: sleep, then listen again
    subst He
    wp_auto
    cleanup_bool_decide
    (try wp_auto)
    wp_apply time.wp_Sleep
    wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp a as %li' %err' HL
    · iframe %Hok
      iapply listen_au $$ Ha
    wp_for_post
    iframe
    iexists li', err'
    iframe l err
    icases HL with (⟨%He', Hli⟩ | ⟨%x, -, #HE⟩)
    · ileft
      iframe Hli
      ipureintro; exact He'
    · iright
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe', rfl⟩ := Hne.2 (by simp)
      iexists pe'
      ipureintro; rfl
  subst He
  wp_auto
  cleanup_bool_decide
  (try wp_auto)
  unfold net.isListener
  icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
  subst Ht
  ipersist l
  ipersist ch
  iclear HΦ
  ihave HI : (∃ fb : Bool, "first" ∷ first_ptr ↦ fb ∗
      "Hlis" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true : IProp GF)
    $$ [first Hlis]
  · iexists true; iframe
  wp_for HI
  wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l x a
      (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true)
      (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
        connEnd (Gg := hG.goose_globalGS) cn true confProto confProto [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn true))
      $$ [Hlis]
    as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hend, -⟩ | ⟨%k, Hlis, #Herr⟩)
  · iframe Hlt Hla
    iapply accept_au a confProto confProto _ l true $$ Ha Hlis
  rotate_left
  · -- a failure: go on
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Herr'
    obtain ⟨pe, rfl⟩ := Herr'.2 (by simp)
    wp_auto
    wp_for_post
    iframe
    iexists fb
    iframe
  subst Herr
  unfold net.isConn
  icases Hc with ⟨%tc, %la, %ra, %Hct, #Hca⟩
  subst Hct
  wp_auto
  unfold connEnd
  icases Hend with ⟨Hsend, Hrecv⟩
  ihave #Hconn := sendTok_connIs cn true confProto [] $$ Hsend
  ihave #Hrd := net.conn_readerOk wp_Read tc cn true a la ra eof ed confProto $$ [$Hio $Hca $Heof $Hed]
  ihave Hsl := slice_array b_ptr 8 _ (by decide) $$ b
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show (W64 8 - W64 0) = W64 8 from rfl]
  ihave HrL := recvTok_L cn true confProto [] $$ Hrecv
  rw [show interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #tc =
    GoInterface.ok (net.connIface tc) from rfl]
  wp_apply wp_ReadFull_lt (net.connIface tc) _ _ _ [] _ _ eof ueof $$ [$Hrd $Hio $Heof $Hueof $HrL $Hsl]
    as %n2 %err2 ⟨%ys, %Hys, Hsl, HrL, #Hres⟩
  · ipureintro; intro ys hys; omega
  rcases err2 with ei | _
  · await_close
  wp_auto
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show (W64 8 - W64 0) = W64 8 from rfl]
  have hl8 : (ys ++ List.drop ys.length (List.replicate 8 (zero_val w8))).length = 8 := by
    have := Hys.2
    have h1 : (zero_val (GoArray w8 8)).arr.length = 8 := rfl
    simp only [List.length_append, List.length_drop, List.length_replicate, h1] at this ⊢; omega
  wp_apply wp_decode _ _ _ hl8 $$ [$Hsl] as %conf %rs %ok ⟨Hsl, Hm⟩
  cases ok
  · await_close
  icases Hm with (%Hf | Hm)
  · cases Hf
  ihave #HP : (□ confProto (GF := GF) cn ([] ++ [W8 107]) : IProp GF) $$ []
  · iintro !>; unfold confProto; itrivial
  iunfold net.connIface at c
  cases fb
  · wp_auto
    await_ack
  · wp_auto
    wp_apply wp_bag_send γch ch _ _ $$ [$Hbag $Hm]
    await_ack

/-- `<-ch` on a configuration channel (`awaitConf`'s): a `msgOk` message. -/
theorem wp_recv_msg (γch : ChanNames) (ch : Loc) :
    {{ isChanBag γch ch (V := msg) (msgOk (hG := hG)) }}
      (App (Val (chan.receive msg.ty)) (Val #ch))
    {{ (m : msg), RET (PairV #m #true); msgOk (hG := hG) m }} :=
  wp_bag_receive γch ch msgOk

/-- `make(chan msg, 1)`: a configuration channel (`newSys`'s and `Server`'s). -/
theorem wp_make_conf_chan :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make2 [go.GoType.ChannelType go.ChanDir.sendrecv msg.ty]))
        (Val #(W64 1)))
    {{ (ch : Loc), RET #ch; ∃ γch, isChanBag γch ch (V := msg) (msgOk (hG := hG)) }} := by
  iintro %Φ - HΦ
  iapply wp_fupd
  wp_apply chan.wp_make2 (V := msg) (W64 1) $$ [] as %ch %γch ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; constructor <;> decide
  imod start_bag (V := msg) (msgOk (hG := hG)) (.Buffered []) ch γch trivial $$ Hch Hoc with #Hbag
  imodintro
  iapply HΦ
  iexists γch
  iexact Hbag

end net

end github_com.despreston.go_craq.examples.craqnet
end Perennial
