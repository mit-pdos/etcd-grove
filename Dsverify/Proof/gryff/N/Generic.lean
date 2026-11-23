/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/Generic.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: program lemmas over a generic `GF` (the concrete `netDistGF` is slow in the kernel and
in `wp_auto`), for `genericsmr`'s functions.
-/
module

public import Dsverify.Proof.gryff.src.gryff.Base
public import Dsverify.GeneratedProof.gryff.src.genericsmr
public import Dsverify.Proof.gryff.Replica.Base
public import Dsverify.Proof.gryff.Wire.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.netN

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section generic
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [gs_sem : gryff.src.genericsmr.Assumptions]

set_option goose.wp.extras true

/-- `ShouldDelayNextRPC(q, code)` with no delay set (`delayRPC[q]` holds only `false`): `false`,
the map now also holding `false` at `code`. -/
theorem wp_ShouldDelayNextRPC (gR : Loc) (dS : GoSlice) (dms : List Loc) (q : Nat) (mp : Loc)
    (M : GMap w8 Bool) (code : w8) (hq : dms[q]? = some mp) (hq3 : q < 3)
    (hM : ∀ c b, M !! c = some b → b = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗
        gR.[gryff.src.genericsmr.Replica, go!"delayRPC"] ↦□ dS ∗ dS ↦*□ dms ∗ mp ↦$ M }}
      (App (App (Val (gR @!! go.GoType.PointerType gryff.src.genericsmr.Replica.ty @!!
        go!"ShouldDelayNextRPC")) (Val #(W64 q))) (Val #code))
    {{ RET #false; mp ↦$ (<[code := false]> M) }} := by
  wp_start as ⟨#Hd, #HdS, Hmp⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ HdS
  have hqZ : sint.Z (W64 (q : Int)) = q := by word
  have hql := (List.getElem?_eq_some_iff.1 hq).1
  have hlenZ : sint.Z (W64 (q : Int)) < sint.Z dS.len := by
    rw [hqZ]; obtain ⟨h1, h2⟩ := Hlen; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, hlenZ⟩)]
  wp_apply wp_load_slice_index dS (sint.Z (W64 (q : Int))) dms DFrac.discard mp (by omega)
    $$ [HdS] as -
  · iframe HdS; ipureintro; rw [hqZ]; simpa using hq
  wp_apply (wp_map_lookup2 (V := Bool) go.uint8 go.bool mp M code (DFrac.own 1)) $$ Hmp as Hmp
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, hlenZ⟩)]
  wp_apply wp_load_slice_index dS (sint.Z (W64 (q : Int))) dms DFrac.discard mp (by omega)
    $$ [HdS] as -
  · iframe HdS; ipureintro; rw [hqZ]; simpa using hq
  wp_apply (wp_mapInsert (V := Bool) go.uint8 mp M code false) $$ Hmp as Hmp
  cases hc : M !! code with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Option.getD_none]
    wp_auto
    iapply HΦ $$ Hmp
  | some b =>
    obtain rfl := hM code b hc
    simp only [Option.isSome_some, decide_true, Option.getD_some]
    wp_auto
    iapply HΦ $$ Hmp

section bufio
variable [bufio.Assumptions]

/-- `WriteByte(c)` on a writer with a sticky error: returns it, writes nothing. -/
theorem wp_WriteByte_sticky (bw : Loc) (wr : wire.WSt GF) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (c : w8) (herr : err ≠ interface.nil) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.ownWriter bw wr J Q sent pend err }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"WriteByte")) (Val #c))
    {{ RET #err; wire.ownWriter bw wr J Q sent pend err }} := by
  iintro %Φ ⟨#Hpkg, Hown⟩ HΦ
  wp_apply wire.wp_WriteByte bw wr J Q sent pend err c $$ [$Hown] as %e1 ⟨%s1, %p1, %H1, Hown⟩
  · iintro %h; exact absurd h herr
  obtain ⟨-, -, -, h4, -⟩ := H1
  obtain ⟨h1, h2, h3⟩ := h4 herr
  subst h1 h2 h3
  iapply HΦ $$ Hown

theorem writerOk_prefixClosed (wr : wire.WSt GF) (J Q : List w8 → IProp GF) :
    wire.writerOk wr J Q ⊢ iprop(□ (∀ (x y : List w8), □ Q (x ++ y) -∗ Q x)) :=
  wire.writerOk_prefixClosed wr J Q

/-- A writer's state as `Marshal`'s general spec starts from: healthy, nothing offered yet; or
failed, with any bytes offered (none will be accepted). -/
theorem wst_of_own (bw : Loc) (wr : wire.WSt GF) (J Q : List w8 → IProp GF)
    (sent pend : List w8) (err : GoInterface) (D : List w8) (h : err = interface.nil → D = []) :
    wire.ownWriter bw wr J Q sent pend err ⊢ wire.wst bw wr J Q sent pend err D := by
  iintro H
  unfold wire.wst
  iexists 0, sent, pend, err
  iframe H
  ipureintro
  refine ⟨Nat.zero_le _, by simp, List.prefix_refl _, fun he => by simp [h he], fun _ => ⟨rfl, rfl⟩⟩

/-- `WriteByte(c)` on a writer that has been handed `X` (healthy or failed). -/
theorem wp_WriteByte_any (bw : Loc) (wr : wire.WSt GF) (J Q : List w8 → IProp GF)
    (sent pend X : List w8) (err : GoInterface) (c : w8)
    (hst : sent ++ pend <+: X ∧ (err = interface.nil → pend = [] ∧ sent = X)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.writerOk wr J Q ∗
        wire.ownWriter bw wr J Q sent pend err ∗ □ Q (X ++ [c]) }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"WriteByte")) (Val #c))
    {{ (e1 : GoInterface), RET #e1; ∃ s1 p1 : List w8, wire.ownWriter bw wr J Q s1 p1 e1 ∗
        ⌜s1 ++ p1 <+: X ++ [c] ∧ (e1 = interface.nil → s1 ++ p1 = X ++ [c])⌝ }} := by
  iintro %Φ ⟨#Hpkg, #Hwr, Hown, #HQ⟩ HΦ
  by_cases herr : err = interface.nil
  · obtain ⟨rfl, rfl⟩ := hst.2 herr
    wp_apply wire.wp_WriteByte bw wr J Q sent [] err c $$ [$Hown] as %e1 ⟨%s1, %p1, %H1, Hown⟩
    · iintro %_; rw [List.append_nil]; iexact HQ
    iapply HΦ
    iexists s1, p1
    iframe Hown
    ipureintro
    rw [List.append_nil] at H1
    by_cases he : e1 = interface.nil
    · have := H1.2.1 he; exact ⟨by rw [this]; exact List.prefix_refl _, fun _ => this⟩
    · have := H1.2.2.1 he; exact ⟨by rw [this]; exact List.prefix_append _ _, fun h => absurd h he⟩
  · wp_apply wp_WriteByte_sticky bw wr J Q sent pend err c herr $$ [$Hown] as Hown
    iapply HΦ
    iexists sent, pend
    iframe Hown
    ipureintro
    exact ⟨hst.1.trans (List.prefix_append _ _), fun h => absurd h herr⟩

/-- The bytes of the writer: `X` handed so far (a prefix of it sent or buffered, all of it sent
when healthy). -/
def wAt (bw : Loc) (wr : wire.WSt GF) (J Q : List w8 → IProp GF) (X : List w8) : IProp GF :=
  iprop(∃ (sent pend : List w8) (err : GoInterface), wire.ownWriter bw wr J Q sent pend err ∗
    ⌜sent ++ pend <+: X ∧ (err = interface.nil → pend = [] ∧ sent = X)⌝)

variable [gp_sem : gryff.src.gryffproto.Assumptions] [dl : gryff.src.dlog.Assumptions]

/-- `pm.Marshal(w)` (the interface call `msg.Marshal(w)` on `msg = (T, pm)`) offers the bytes `e`
to any writer (`Wire/Specs.lean`'s general form), with the message's resources `R`. -/
def marSpec (T : go.GoType) (pm : Loc) (e : List w8) (R : IProp GF) : Prop :=
  ∀ (w : Loc) (wr : wire.WSt GF) (J Q : List w8 → IProp GF) (s p : List w8) (er : GoInterface)
    (E0 D : List w8),
    {{ wire.writerOk wr J Q ∗ □ Q (s ++ p ++ E0) ∗ ⌜D ++ e <+: E0⌝ ∗
        wire.wst w wr J Q s p er D ∗ R }}
      (App (Val (pm @!! T @!! go!"Marshal"))
        (Val #(interface.mkOk (go.GoType.PointerType bufio.Writer.ty) #w)))
    {{ RET #(); wire.wst w wr J Q s p er (D ++ e) ∗ R }}

/-- The final writer state of `SendMsg` (pure). -/
theorem sendmsg_final (X e s1 p1 s2 p2 D : List w8) (c : w8) (e1 e2 e3 : GoInterface) (k k' : Nat)
    (h1 : s1 ++ p1 <+: X ++ [c]) (h1n : e1 = interface.nil → s1 ++ p1 = X ++ [c])
    (hD : D = (X ++ [c]).drop (s1 ++ p1).length)
    (h2 : s2 ++ p2 = s1 ++ p1 ++ (D ++ e).take k) (h2n : e2 = interface.nil → k = (D ++ e).length)
    (h2e : e1 ≠ interface.nil → e2 = e1 ∧ k = 0)
    (h3n : e3 = interface.nil → k' = p2.length) (h3e : e2 ≠ interface.nil → e3 = e2 ∧ k' = 0) :
    (s2 ++ p2.take k') ++ p2.drop k' <+: X ++ c :: e ∧
      (e3 = interface.nil → p2.drop k' = [] ∧ s2 ++ p2.take k' = X ++ c :: e) := by
  obtain ⟨z, hz⟩ := h1
  have hDz : D = z := by rw [hD, ← hz, List.drop_left]
  have hY : s1 ++ p1 ++ (D ++ e) = X ++ c :: e := by
    rw [hDz, ← List.append_assoc, hz]; simp
  have hs : (s2 ++ p2.take k') ++ p2.drop k' = s1 ++ p1 ++ (D ++ e).take k := by
    rw [List.append_assoc, List.take_append_drop, h2]
  refine ⟨?_, fun he3 => ?_⟩
  · rw [hs, ← hY]
    exact (List.prefix_append_right_inj _).2 (List.take_prefix _ _)
  · have he2 : e2 = interface.nil := by
      rcases Classical.em (e2 = interface.nil) with h | hne
      · exact h
      · exact absurd (((h3e hne).1).symm.trans he3) hne
    have hk' := h3n he3
    refine ⟨by rw [hk', List.drop_length], ?_⟩
    rw [hk', List.take_length, h2, h2n he2, List.take_length, hY]

theorem wp_SendMsg_gen (gR : Loc) (q : Nat) (hq3 : q < 3) (code : w8) (T : go.GoType) (pm : Loc)
    (dS : GoSlice) (dms : List Loc) (mp : Loc) (M : GMap w8 Bool) (hq : dms[q]? = some mp)
    (hM : ∀ c b, M !! c = some b → b = false) (pwS : GoSlice) (pws : List Loc) (w : Loc)
    (hw : pws[q]? = some w) (myId : w32) (wr : wire.WSt GF) (J Q : List w8 → IProp GF)
    (X e : List w8) (R : IProp GF) (hmar : marSpec T pm e R) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog ∗
        globalAddr gryff.src.dlog.DLOG ↦□ false ∗
        gR.[gryff.src.genericsmr.Replica, go!"delayRPC"] ↦□ dS ∗ dS ↦*□ dms ∗ mp ↦$ M ∗
        gR.[gryff.src.genericsmr.Replica, go!"PeerWriters"] ↦□ pwS ∗ pwS ↦*□ pws ∗
        gR.[gryff.src.genericsmr.Replica, go!"Id"] ↦□ myId ∗
        wire.writerOk wr J Q ∗ wAt w wr J Q X ∗ □ Q (X ++ code :: e) ∗ R }}
      (App (App (App (Val (gR @!! go.GoType.PointerType gryff.src.genericsmr.Replica.ty @!!
        go!"SendMsg")) (Val #(W32 q))) (Val #code)) (Val #(interface.mkOk T #pm)))
    {{ RET #(); mp ↦$ (<[code := false]> M) ∗ R ∗ wAt w wr J Q (X ++ code :: e) }} := by
  wp_start as ⟨#Hdlog, #Hd, #HdS, Hmp, #Hpw, #HpwS, #HId, #Hwr, Hw, #HQ, HR⟩
  wp_auto
  have hqZ : W64 (sint.Z (W32 (q : Int))) = W64 (q : Int) := by word
  rw [hqZ]
  wp_apply wp_ShouldDelayNextRPC gR dS dms q mp M code hq hq3 hM $$ [$Hd $HdS $Hmp] as Hmp
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
  ihave %Hlen := ownSlice_len _ _ _ $$ HpwS
  have hql := (List.getElem?_eq_some_iff.1 hw).1
  have hqZ2 : sint.Z (W64 (sint.Z (W32 (q : Int)))) = q := by word
  have hlenZ : sint.Z (W64 (sint.Z (W32 (q : Int)))) < sint.Z pwS.len := by
    rw [hqZ2]; obtain ⟨h1, h2⟩ := Hlen; simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, hlenZ⟩)]
  wp_apply wp_load_slice_index pwS _ pws DFrac.discard w (by omega) $$ [HpwS] as -
  · iframe HpwS; ipureintro; rw [hqZ2]; simpa using hw
  iunfold wAt at Hw
  icases Hw with ⟨%sent, %pend, %err, Hown, %Hst⟩
  ihave #Hpc := writerOk_prefixClosed $$ Hwr
  ihave #HQc := EtcdGrove.bufio.Q_of_prefix Q (X ++ [code]) (X ++ code :: e) (by simp) $$ Hpc HQ
  wp_apply wp_WriteByte_any w wr J Q sent pend X err code Hst $$ [$Hwr $Hown $HQc]
    as %e1 ⟨%s1, %p1, Hown, %H1⟩
  ihave Hw := wst_of_own w wr J Q s1 p1 e1 ((X ++ [code]).drop (s1 ++ p1).length)
    (fun he => by rw [H1.2 he]; simp) $$ Hown
  wp_apply hmar w wr J Q s1 p1 e1 ((X ++ [code]).drop (s1 ++ p1).length ++ e)
    ((X ++ [code]).drop (s1 ++ p1).length) $$ [$Hwr $Hw $HR] as ⟨Hw, HR⟩
  · isplitl
    · obtain ⟨z, hz⟩ := H1.1
      have : s1 ++ p1 ++ ((X ++ [code]).drop (s1 ++ p1).length ++ e) = X ++ code :: e := by
        rw [← hz, List.drop_left, ← List.append_assoc, hz]; simp
      rw [this]; iexact HQ
    · ipureintro; exact List.prefix_refl _
  iunfold wire.wst at Hw
  icases Hw with ⟨%k, %s2, %p2, %e2, %H2, Hown⟩
  wp_apply wire.wp_Flush w wr J Q s2 p2 e2 $$ [$Hown] as %e3 ⟨%k', %H3, Hown⟩
  iapply HΦ
  iframe Hmp HR
  iunfold wAt
  iexists _, _, _
  iframe Hown
  ipureintro
  exact sendmsg_final X e s1 p1 s2 p2 _ code e1 e2 e3 k k' H1.1 H1.2 rfl H2.2.1 H2.2.2.2.1
    H2.2.2.2.2 H3.2.1 H3.2.2

end bufio

end generic

end Perennial.gryff.netN
