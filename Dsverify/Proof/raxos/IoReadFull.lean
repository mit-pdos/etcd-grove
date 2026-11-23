/-
**`io.ReadAtLeast`/`io.ReadFull` with the premise asked only of the reads they make** (a local copy
of Perennial branch `readatleast-prefix`, `af905abba`, off `lean` `7b2259a12`;
notes/perennial-changes.md, 2026-11-23, "`io.ReadFull`/`io.ReadAtLeast` ask `Pre` of a read they
never make"): Perennial's specs at the pin ask the reader's condition `Pre` of an empty read,
which a connection's (`net.conn_readerOk`, `0 < m`) refuses, so the proxy's
`io.ReadFull(conn, bs)` (its 4-byte handshake, `waitForConnections`) cannot use them. These are
that branch's statements and proofs, over Perennial's translation of `io.go`, under the names
`raxos.ioLt.*`; drop them when the pin reaches the branch.
-/
module

public import Perennial.Proof.io.Reader

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

/-- `io.ReadAtLeast(r, buf, min)` of a reader `r` keeping the contract `Pre`, `S`, `E`
(`io.readerOk`), from `S r0`: delivers `ys` into the front of `buf` and leaves `S (r0 ++ ys)`,
returning `len(ys)` and an error as `io.readAtLeastRes` says (`eof`, `ueof`, `sb`: the values of
`io.EOF`, `io.ErrUnexpectedEOF`, `io.ErrShortBuffer`). Each `Read` is of `buf`'s remaining bytes,
after `ys` with `len(ys) < min` and `len(ys) < len(buf)` (the loop reads only while `n < min`, and
only once `min ≤ len(buf)`: else it returns `ErrShortBuffer` at once), so `Pre` must hold of every
such call, never of an empty read (a reader whose condition refuses `len(p) = 0`, a connection's,
qualifies). It may not return (a reader that keeps returning `0, nil`:
partial correctness). -/
abbrev raxos.ioLt.ReadAtLeast.spec : Prop :=
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
        io.readAtLeastRes E eof ueof sb r0 ys xs.length (sint.Z min) err }}

end spec



open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

theorem raxos.ioLt.ReadAtLeast.wp_proof :
    raxos.ioLt.ReadAtLeast.spec (GF := GF) (hG := hG) := by
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

end proof



open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

/-- `io.ReadFull(r, buf)` of a reader `r` keeping the contract `Pre`, `S`, `E`
(`io.readerOk`), from `S r0`: delivers `ys` into the front of `buf` and leaves `S (r0 ++ ys)`,
returning `len(ys)` and an error as `io.readFullRes` says (`nil` when all came; else the
reader's last error with its evidence, or `io.ErrUnexpectedEOF` for an `io.EOF` after some
bytes; `eof`, `ueof`: the values of `io.EOF`, `io.ErrUnexpectedEOF`). Each `Read` is of `buf`'s
remaining bytes, never empty (the loop reads only while some are left), so `Pre` must hold of every
such call. It may not return (a reader that keeps
returning `0, nil`: partial correctness). -/
abbrev raxos.ioLt.ReadFull.spec : Prop :=
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
        io.readFullRes E eof ueof r0 ys xs.length err }}

end spec



open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

theorem raxos.ioLt.ReadFull.wp_proof
    (wp_ReadAtLeast : raxos.ioLt.ReadAtLeast.spec (GF := GF) (hG := hG)) :
    raxos.ioLt.ReadFull.spec (GF := GF) (hG := hG) := by
  intro ri Pre S E r0 p xs eof ueof
  wp_start as ⟨#Hr, #Heof, #Hueof, %Hpre, HS, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hp
  ihave Hi := io.isInit_access $$ Hpkg
  icases Hi with ⟨-, -, -, HSB, -⟩
  iunfold errors.newVar at HSB
  icases HSB with ⟨%xsb, #HSB, -⟩
  wp_auto
  wp_apply wp_ReadAtLeast ri Pre S E r0 p xs p.len eof ueof _ $$ [Hp HS]
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

end proof


end Perennial
