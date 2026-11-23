/-
`io.ReadFull` over a reader whose contract asks a condition only of reads that `ReadAtLeast` makes
(`ys.length < xs.length`: it reads only while it has fewer bytes than asked), such as a
connection's (`net.conn_readerOk`: a non-empty buffer). Perennial's `io.ReadAtLeast.spec` asks the
condition at every `ys.length ≤ xs.length`, the full buffer included, which a connection's
contract does not meet (the gap dsv-bufio records as review C1; Perennial branch
`readatleast-prefix` changes the premise). Until it lands: `io.ReadAtLeast.wp_proofLt`, a copy of
Perennial's proof (`Perennial/Proof/io/ReadAtLeast.lean`, Perennial `9c3b81f3`) with the weaker
premise (one line changed), and `io.ReadFull.wp_proofLt` over it; then `wp_connReadFull`, a
connection end's `io.ReadFull` (the kit's `sendConf` and `awaitConf` read a connection with
`io.ReadFull` directly).
-/
module

public import Perennial.Spec.io.ReadAtLeast
public import Perennial.Spec.io.ReadFull
public import Net.Proof.net.ConnIo
public import Net.Proof.net.Conn__Read

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.examples.rabianet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `io.ReadAtLeast.spec` with the condition asked only below the buffer's length. -/
abbrev io.ReadAtLeast.specLt : Prop :=
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r0 : List w8) (p : GoSlice) (xs : List w8)
    (min : w64) (eof ueof sb : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ _root_.Perennial.io.readerOk ri Pre S E ∗
      globalAddr _root_.Perennial.io.EOF ↦□ eof ∗ globalAddr _root_.Perennial.io.ErrUnexpectedEOF ↦□ ueof ∗
      globalAddr _root_.Perennial.io.ErrShortBuffer ↦□ sb ∗
      ⌜∀ ys : List w8, ys.length < xs.length → Pre (r0 ++ ys) (xs.length - ys.length)⌝ ∗
      S r0 ∗ p ↦* xs }}
    (App (App (App (Val (@! _root_.Perennial.io.ReadAtLeast)) (Val #(interface.ok ri))) (Val #p)) (Val #min))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ S (r0 ++ ys) ∗
        _root_.Perennial.io.readAtLeastRes E eof ueof sb r0 ys xs.length (sint.Z min) err }}

/-- `io.ReadFull.spec` with the condition asked only below the buffer's length. -/
abbrev io.ReadFull.specLt : Prop :=
  ∀ (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (r0 : List w8) (p : GoSlice) (xs : List w8)
    (eof ueof : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ _root_.Perennial.io.readerOk ri Pre S E ∗
      globalAddr _root_.Perennial.io.EOF ↦□ eof ∗ globalAddr _root_.Perennial.io.ErrUnexpectedEOF ↦□ ueof ∗
      ⌜∀ ys : List w8, ys.length < xs.length → Pre (r0 ++ ys) (xs.length - ys.length)⌝ ∗
      S r0 ∗ p ↦* xs }}
    (App (App (Val (@! _root_.Perennial.io.ReadFull)) (Val #(interface.ok ri))) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ S (r0 ++ ys) ∗
        _root_.Perennial.io.readFullRes E eof ueof r0 ys xs.length err }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.io.Assumptions]

theorem io.ReadAtLeast.wp_proofLt :
    io.ReadAtLeast.specLt (GF := GF) (hG := hG) := by
  intro ri Pre S E r0 p xs min eof ueof sb
  wp_start as ⟨#Hr, #Heof, #Hueof, #Hsb, %Hpre, HS, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hp
  ihave %Hwf := ownSlice_wf $$ Hp
  -- `EOF`'s value is a `*errorString`
  ihave HEOF := _root_.Perennial.io.eof_of_init $$ Hpkg
  iunfold _root_.Perennial.errors.newVar at HEOF
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
    unfold _root_.Perennial.io.readAtLeastRes
    ileft; ipureintro
    exact ⟨by word, rfl, rfl⟩
  have Hmin : sint.Z min ≤ (xs.length : Int) := by word
  ihave HI : (∃ (n : w64) (ev : GoInterface) (ys : List w8),
      "n" ∷ n_ptr ↦ n ∗ "err" ∷ err_ptr ↦ ev ∗
      "Hp" ∷ p ↦* (ys ++ xs.drop ys.length) ∗ "HS" ∷ S (r0 ++ ys) ∗
      "#Herr" ∷ _root_.Perennial.io.errAt E (r0 ++ ys) ev ∗ "%Hty" ∷ ⌜_root_.Perennial.io.ptrTyped ev⌝ ∗
      "%Hys" ∷ ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length⌝ : IProp GF) $$ [n err Hp HS]
  · iexists _, _, []
    simp only [List.nil_append, List.drop_zero, List.append_nil, List.length_nil]
    iframe
    isplit
    · unfold _root_.Perennial.io.errAt; ileft; ipureintro; rfl
    ipureintro
    exact ⟨_root_.Perennial.io.ptrTyped_nil, by simp only [zero_val, ZeroVal.zeroValDef]; word, by omega⟩
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
      have hlt : ys.length < xs.length := by
        exact Int.ofNat_lt.mp (Int.lt_of_lt_of_le (Hys.1 ▸ Hif) Hmin)
      wp_apply _root_.Perennial.io.wp_reader_Read ri Pre S E (r0 ++ ys) _ (xs.drop ys.length)
          (by rw [List.length_drop]; exact Hpre ys hlt) $$ [Hp2 HS]
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
            unfold _root_.Perennial.io.readAtLeastRes _root_.Perennial.io.errAt
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
            unfold _root_.Perennial.io.readAtLeastRes _root_.Perennial.io.errAt
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
          unfold _root_.Perennial.io.readAtLeastRes _root_.Perennial.io.errAt
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
        unfold _root_.Perennial.io.readAtLeastRes _root_.Perennial.io.errAt
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
      unfold _root_.Perennial.io.readAtLeastRes
      iright; ileft
      ipureintro
      exact ⟨Hmin, by word, rfl⟩
    · exfalso; word


theorem io.ReadFull.wp_proofLt : io.ReadFull.specLt (GF := GF) (hG := hG) := by
  intro ri Pre S E r0 p xs eof ueof
  wp_start as ⟨#Hr, #Heof, #Hueof, %Hpre, HS, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hp
  ihave Hi := _root_.Perennial.io.isInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, HSB, -⟩
  iunfold _root_.Perennial.errors.newVar at HSB
  icases HSB with ⟨%xsb, #HSB, -⟩
  wp_auto
  wp_apply io.ReadAtLeast.wp_proofLt ri Pre S E r0 p xs p.len eof ueof _ $$ [Hp HS]
    as %n %err ⟨%ys, %Hys, Hp, HS, #Hres⟩
  · iframe Hr Heof Hueof HSB HS Hp
    ipureintro; exact Hpre
  wp_auto
  iapply HΦ
  iexists ys
  iframe Hp HS
  isplit
  · ipureintro; exact Hys
  have hm : sint.Z p.len = ((xs.length : Nat) : Int) := by word
  rw [hm]
  iapply _root_.Perennial.io.readFullRes_of_readAtLeastRes E eof ueof _ r0 ys xs.length err Hys.2 $$ Hres

end proof

section conn
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [_root_.Perennial.io.Assumptions] [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- `io.ReadFull(c, p)` of the end `s` of the connection `cn` (its `*TCPConn` `t`): what it read
extends the reader's token; no error only if it filled `p`. -/
theorem wp_connReadFull (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra ed : GoInterface)
    (P : Proto GF) (r0 : List w8) (p : GoSlice) (xs : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ net.connAt t cn s a la ra ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ∗
        recvTokL (Gg := hG.goose_globalGS) cn s P r0 ∗ p ↦* xs }}
      (App (App (Val (@! _root_.Perennial.io.ReadFull))
        (Val #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t))) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length ∧
          (err = interface.nil → ys.length = xs.length)⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ recvTokL (Gg := hG.goose_globalGS) cn s P (r0 ++ ys) }} := by
  iintro %Φ ⟨#Hio, #Hc, #Hed, HS, Hp⟩ HΦ
  ihave #Hi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  iunfold _root_.Perennial.errors.newVar at HEOF HUEOF
  icases HEOF with ⟨%x1, #Heof, -⟩
  icases HUEOF with ⟨%x2, #Hueof, -⟩
  ihave #Hrok := net.conn_readerOk net.Conn.Read.wp_proof t cn s a la ra _ ed P $$ [$Hio $Hc $Heof $Hed]
  rw [show interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t = GoInterface.ok (net.connIface t)
    from rfl]
  iapply io.ReadFull.wp_proofLt (net.connIface t) (fun _ m => 0 < m)
    (recvTokL (Gg := hG.goose_globalGS) cn s P) _ r0 p xs _ _ $$ [HS Hp]
  · iframe Hio Hrok Heof Hueof HS Hp
    ipureintro
    intro ys h; show 0 < xs.length - ys.length; omega
  inext
  iintro %n %err ⟨%ys, %Hys, Hp, HS, #Hres⟩
  unfold _root_.Perennial.io.readFullRes
  ihave %Himp : ⌜err = interface.nil → ys.length = xs.length⌝ $$ [Hres]
  · icases Hres with (%h | ⟨%e, %h, -⟩)
    · ipureintro; exact fun _ => h.1
    · ipureintro
      obtain ⟨hlt, hne, h1, h2⟩ := h
      intro he
      exfalso
      by_cases hc : e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x1 ∧ ys ≠ []
      · rw [h1 hc] at he; simp [interface.mkOk] at he
      · rw [h2 hc] at he; exact hne he
  iapply HΦ
  iexists ys
  iframe Hp HS
  ipureintro
  exact ⟨Hys.1, Hys.2, Himp⟩

end conn

end Perennial.rabia.examples.rabianet
