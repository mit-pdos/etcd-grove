/-
Ported from dsverify-lab examples/epaxos/proof/Epaxos/Proof/wire/WProg.lean (notes/dsv-epaxos.md),
restated over dsv-bufio's `*bufio.Writer` (`wrOwn`, `BufWr`; `Writer.Write.spec`,
`Writer.WriteByte.spec`, whose sticky-error clauses replace the lab's `BufioSticky`).

A marshaler's progress on a `*bufio.Writer` (internal to the wire package): `wprog … done todo`
says that, from the writer's state `(sent, pend, err)` at the marshaler's start, the writer has
accepted a prefix of `done` (`wroteSome`), and the whole encoding `done ++ todo` is allowed when
the writer was healthy at the start. Each write moves bytes from `todo` to `done`
(`wp_wprog_Write`, `wp_wprog_WriteByte`, `wp_wprog_marshal`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Marshal
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.LibDeps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## `wroteSome` -/

section ws
variable [GooseExts]

theorem wroteSome_nil (sent pend : List w8) (err : GoInterface) :
    wroteSome sent pend [] sent pend err err := by
  refine ⟨List.prefix_refl _, List.prefix_refl _, by simp, by simp, fun _ => ⟨rfl, rfl⟩⟩

theorem wroteSome_trans (s p a b s1 p1 s2 p2 : List w8) (err e1 e2 : GoInterface)
    (h1 : wroteSome s p a s1 p1 err e1) (h2 : wroteSome s1 p1 b s2 p2 e1 e2) :
    wroteSome s p (a ++ b) s2 p2 err e2 := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2
  refine ⟨a1.trans b1, a2.trans b2, ?_, ?_, ?_⟩
  · by_cases he : e1 = interface.nil
    · rw [a4 he] at b3; simpa using b3
    · rw [(b5 he).2]
      exact a3.trans (by rw [← List.append_assoc]; exact List.prefix_append _ _)
  · intro he2
    have he1 : e1 = interface.nil :=
      Classical.byContradiction fun h => h ((b5 h).1 ▸ he2)
    rw [b4 he2, a4 he1]; simp
  · intro herr
    obtain ⟨c1, c2⟩ := a5 herr
    obtain ⟨d1, d2⟩ := b5 (c1 ▸ herr)
    exact ⟨d1.trans c1, d2.trans c2⟩

/-- `Write'`'s outcome as `wroteSome`. -/
theorem wroteSome_of_write (sent pend ps sent' pend' : List w8) (err e : GoInterface) (k : Nat)
    (h1 : k ≤ ps.length) (h2 : sent' ++ pend' = sent ++ pend ++ ps.take k) (h3 : sent <+: sent')
    (h4 : e = interface.nil → k = ps.length)
    (h5 : err ≠ interface.nil → e = err ∧ k = 0 ∧ sent' = sent ∧ pend' = pend) :
    wroteSome sent pend ps sent' pend' err e := by
  refine ⟨h3, ?_, ?_, ?_, ?_⟩
  · rw [h2]; exact List.prefix_append _ _
  · rw [h2, List.append_assoc, List.append_assoc]
    exact (List.prefix_append_right_inj _).mpr ((List.prefix_append_right_inj _).mpr
      (List.take_prefix _ _))
  · intro he; rw [h2, h4 he, List.take_length]
  · intro he; obtain ⟨r1, r2, -⟩ := h5 he; refine ⟨r1, ?_⟩; rw [h2, r2]; simp

/-- `WriteByte'`'s outcome as `wroteSome`. -/
theorem wroteSome_of_writeByte (sent pend sent' pend' : List w8) (err e : GoInterface) (c : w8)
    (h1 : sent <+: sent') (h2 : e = interface.nil → sent' ++ pend' = sent ++ pend ++ [c])
    (h3 : e ≠ interface.nil → sent' ++ pend' = sent ++ pend)
    (h4 : err ≠ interface.nil → e = err ∧ sent' = sent ∧ pend' = pend) :
    wroteSome sent pend [c] sent' pend' err e := by
  refine ⟨h1, ?_, ?_, h2, fun he => ⟨(h4 he).1, h3 ((h4 he).1 ▸ he)⟩⟩
  · by_cases he : e = interface.nil
    · rw [h2 he]; exact List.prefix_append _ _
    · rw [h3 he]; exact List.prefix_refl _
  · by_cases he : e = interface.nil
    · rw [h2 he]; exact List.prefix_refl _
    · rw [h3 he]; exact List.prefix_append _ _

end ws

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [bufio.Assumptions]

attribute [local instance] BufRd.F_persistent

/-- See the file header. -/
def wprog (bw : Loc) (wr : BufWr GF) (sent pend : List w8)
    (err : GoInterface) (done todo : List w8) : IProp GF :=
  iprop(□ (⌜err = interface.nil⌝ → □ wr.Q (sent ++ pend ++ done ++ todo)) ∗
    ∃ (s' p' : List w8) (e : GoInterface), ⌜wroteSome sent pend done s' p' err e⌝ ∗
      wrOwn bw wr s' p' e)

theorem wprog_start (bw : Loc) (wr : BufWr GF)
    (sent pend : List w8) (err : GoInterface) (bs : List w8) :
    (wrOwn bw wr sent pend err ∗
      (⌜err = interface.nil⌝ -∗ □ wr.Q (sent ++ pend ++ bs))) ⊢
      wprog bw wr sent pend err [] bs := by
  iintro ⟨Hown, HQ⟩
  unfold wprog
  rcases err with ei | _
  · iclear HQ
    isplitl []
    · imodintro; iintro %h; exact absurd h (by simp)
    iexists sent, pend, _
    iframe Hown
    ipureintro; exact wroteSome_nil _ _ _
  · ihave #HQ' := HQ $$ %rfl
    isplitl []
    · imodintro; iintro %_; simp only [List.append_nil]; iexact HQ'
    iexists sent, pend, _
    iframe Hown
    ipureintro; exact wroteSome_nil _ _ _

theorem wprog_finish (bw : Loc) (wr : BufWr GF)
    (sent pend : List w8) (err : GoInterface) (done bs : List w8) (h : done = bs) :
    wprog bw wr sent pend err done [] ⊢
      ∃ (sent' pend' : List w8) (e : GoInterface),
        ⌜wroteSome sent pend bs sent' pend' err e⌝ ∗ wrOwn bw wr sent' pend' e := by
  subst h
  iintro H
  iunfold wprog at H
  icases H with ⟨-, H⟩
  iexact H

/-- The protocol obligation for the next write, from the progress. -/
theorem wprog_obl (wr : BufWr GF) (sent pend done x todo s' p' : List w8)
    (err e : GoInterface) (hw : wroteSome sent pend done s' p' err e) :
    □ (⌜err = interface.nil⌝ → □ wr.Q (sent ++ pend ++ done ++ (x ++ todo)))
      ⊢ (⌜e = interface.nil⌝ -∗ □ wr.Q (s' ++ p' ++ x)) := by
  iintro #HQ %he
  have herr : err = interface.nil :=
    Classical.byContradiction fun h => h ((hw.2.2.2.2 h).1 ▸ he)
  ihave #HQ1 := HQ $$ %herr
  have hs : s' ++ p' = sent ++ pend ++ done := hw.2.2.2.1 he
  have hpre : □ wr.Q (sent ++ pend ++ done ++ (x ++ todo)) ⊢ □ wr.Q (s' ++ p' ++ x) := by
    rw [hs]
    have := wr.Q_pre (sent ++ pend ++ done ++ x) todo
    simpa only [List.append_assoc] using this
  iapply hpre
  iexact HQ1

set_option goose.wp.extras true

variable [EpBufioDeps GF]

/-- `bw.Write(p)` (on the `*bufio.Writer`) with the next bytes `x` of the encoding. -/
theorem wp_wprog_Write (bw : Loc) (wr : BufWr GF)
    (sent pend : List w8) (err : GoInterface) (done rest x todo : List w8) (p : GoSlice)
    (dq : DFrac) (hr : rest = x ++ todo) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗
        wprog bw wr sent pend err done rest ∗ p ↦*{dq} x }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"Write")) (Val #p))
    {{ (nn : w64) (e : GoInterface), RET (PairV #nn #e); p ↦*{dq} x ∗
        wprog bw wr sent pend err (done ++ x) todo }} := by
  subst hr
  iintro %Φ ⟨#Hpkg, Hw, Hp⟩ HΦ
  iunfold wprog at Hw
  icases Hw with ⟨#HQ, %s', %p', %e, %hw, Hown⟩
  ihave HQx := wprog_obl wr sent pend done x todo s' p' err e hw $$ HQ
  wp_apply EpBufioDeps.write bw wr.wi wr.J wr.Q wr.Ew wr.sz s' p' e p dq x
    $$ [$Hown $HQx $Hp]
    as %nn %e2 ⟨%k, %s2, %p2, %Hk, Hp, Hown⟩
  obtain ⟨-, h1, h2, h3, h4, h5, -⟩ := Hk
  iapply HΦ
  iframe Hp
  unfold wprog
  isplitl []
  · imodintro; iintro %h; ihave #H := HQ $$ %h; simp only [List.append_assoc]
    simp only [List.append_assoc] at *; iexact H
  iexists s2, p2, e2
  iframe Hown
  ipureintro
  exact wroteSome_trans _ _ _ _ _ _ _ _ _ _ _ hw
    (wroteSome_of_write _ _ _ _ _ _ _ k h1 h2 h3 h4 h5)

/-- `bw.WriteByte(c)` with the next byte `c` of the encoding. -/
theorem wp_wprog_WriteByte (bw : Loc) (wr : BufWr GF)
    (sent pend : List w8) (err : GoInterface) (done rest todo : List w8) (c : w8)
    (hr : rest = c :: todo) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗
        wprog bw wr sent pend err done rest }}
      (App (Val (bw @!! go.GoType.PointerType bufio.Writer.ty @!! go!"WriteByte")) (Val #c))
    {{ (e : GoInterface), RET #e; wprog bw wr sent pend err (done ++ [c]) todo }} := by
  subst hr
  iintro %Φ ⟨#Hpkg, Hw⟩ HΦ
  iunfold wprog at Hw
  icases Hw with ⟨#HQ, %s', %p', %e, %hw, Hown⟩
  have hob := wprog_obl wr sent pend done [c] todo s' p' err e hw
  simp only [List.singleton_append] at hob
  ihave HQx := hob $$ HQ
  wp_apply EpBufioDeps.writeByte
    bw wr.wi wr.J wr.Q wr.Ew wr.sz s' p' e c
    $$ [$Hown $HQx]
    as %e2 ⟨%s2, %p2, %Hk, Hown⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := Hk
  iapply HΦ
  unfold wprog
  isplitl []
  · imodintro; iintro %h; ihave #H := HQ $$ %h
    simp only [List.append_assoc, List.singleton_append] at *; iexact H
  iexists s2, p2, e2
  iframe Hown
  ipureintro
  exact wroteSome_trans _ _ _ _ _ _ _ _ _ _ _ hw
    (wroteSome_of_writeByte _ _ _ _ _ _ c h1 h2 h3 h4)

/-- A nested `Marshal(w)` (by its `marshalTriple`) writing the next bytes `x`. -/
theorem wp_wprog_marshal (pkg : IProp GF) [Persistent pkg] (fn : val)
    (Rs : IProp GF) (x : List w8) (hm : marshalTriple pkg fn Rs x)
    (bw : Loc) (wr : BufWr GF)
    (sent pend : List w8) (err : GoInterface) (done rest todo : List w8)
    (hr : rest = x ++ todo) :
    {{ pkg ∗ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗
        wprog bw wr sent pend err done rest ∗ Rs }}
      (App (Val fn) (Val #(bwIface bw)))
    {{ RET #(); Rs ∗ wprog bw wr sent pend err (done ++ x) todo }} := by
  subst hr
  iintro %Φ ⟨#Hpk, #Hpkg, Hw, HR⟩ HΦ
  iunfold wprog at Hw
  icases Hw with ⟨#HQ, %s', %p', %e, %hw, Hown⟩
  ihave HQx := wprog_obl wr sent pend done x todo s' p' err e hw $$ HQ
  wp_apply hm bw wr s' p' e $$ [$Hpk $Hpkg $Hown $HQx $HR]
    as ⟨HR, %s2, %p2, %e2, %hw2, Hown⟩
  iapply HΦ
  iframe HR
  unfold wprog
  isplitl []
  · imodintro; iintro %h; ihave #H := HQ $$ %h
    simp only [List.append_assoc] at *; iexact H
  iexists s2, p2, e2
  iframe Hown
  ipureintro
  exact wroteSome_trans _ _ _ _ _ _ _ _ _ _ _ hw hw2

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
