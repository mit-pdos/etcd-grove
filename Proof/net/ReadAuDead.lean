/-
`read_au_dead`: the net extension's `read_au` with what a read that returns EOF, a `sys` error or
`closed` leaves, for a reader that does not hold the read deadline's `rdlTok` (the encoding/json
model's `Decoder`, `Proof/encoding/json/Codec/Decoder__fetch_conn.lean`). A lemma over the
extension's ghost state (`GooseLang/Ext/Net/Proto.lean`), proved as its `read_dead_au` is. Lean-first
(no Rocq counterpart).
-/
module

public import GooseLang.Ext.Net.Proto

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace Net

section access
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]
variable [NetProtoGS]
include Gg

set_option warn.classDefReducibility false in
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `read_au` with what a read that returns EOF, a `sys` error or `closed` leaves (D1 v3.5): the end's
reading dead for good (`readDead`), as `read_dead_au` gives without the read deadline's `rdlTok` (a
reader that does not hold it: the encoding/json model's `Decoder`, which reads again after EOF,
`read_after_dead_au`). -/
theorem read_au_dead (cn : Nat) (s : Bool) (P : Proto GF) (R : List w8) (n : Nat) :
    recvTokL (Gg := Gg) cn s P R ⊢
      |={⊤,∅}=> ∃ st d, netEnd NG cn s st ∗ netDir NG cn (!s) d ∗
        ∀ r d', ⌜ReadOutcome st d n r d'⌝ -∗ netEnd NG cn s st -∗ netDir NG cn (!s) d' ={∅,⊤}=∗
          recvTokL cn s P (R ++ r.got) ∗ ⌜∃ st d d', ReadOutcome st d n r d'⌝ ∗
          (⌜r = .eof ∨ r = .err .sys ∨ r = .err .closed⌝ -∗ readDead cn s) := by
  unfold recvTokL recvCore connH
  iintro ⟨⟨%γ, %Pd, %Pa, ⟨#He, #Hreg, #Hai, #Hm⟩, %hP, Hr, #Hlb⟩, -⟩
  imod reg_open_full cn γ s (!s) $$ Hreg He
    with ⟨%st, %d, %W, %R0, %x, %c, Hend, Hdir, HwQ, Hr0, Hrd, Hx, Hcc, %Hok, Hcl⟩
  imod addr_open (⊤ \ ↑regN) γ.addr γ.am Pd Pa cn γ (!s) (addrN_regN γ.addr) $$ Hai Hm
    with ⟨%W2, HwQ2, Hpp, Hcl2⟩
  icases w_agree_qq (γ.w (!s)) _ _ $$ HwQ HwQ2 with %h1
  icases r_agree (γ.r (!s)) _ _ $$ Hr Hr0 with %h2
  subst h1 h2
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hdir
  iintro %r %d' %Hro Hend Hdir
  imod Hmask
  have Hok' := dirOk_read Hok.1 Hro
  imod r_update (γ.r (!s)) _ _ (R ++ r.got) $$ Hr Hr0 with ⟨Hr, Hr0⟩
  ihave #Hlb' := wQ_lb (γ.w (!s)) W $$ HwQ
  ihave #Hlb' := wLb_le (γ.w (!s)) (R ++ r.got) (dirOk_prefix Hok') $$ Hlb'
  ihave #Hpp' : ▷ protoPrefix (sel (!s) Pd Pa) cn (R ++ r.got) $$ [Hpp]
  · iapply later_mono (protoPrefix_le (dirOk_prefix Hok'))
    iexact Hpp
  imod Hcl2 $$ HwQ2 Hpp with -
  imod mono_nat_own_update (GF := GF) (max x (if r = .eof ∨ r = .err .sys then 1 else 0))
    (Nat.le_max_left _ _) $$ Hx with ⟨Hx, #Hxlb⟩
  imod mono_nat_own_update (GF := GF) (max c (if r = .err .closed then 1 else 0))
    (Nat.le_max_left _ _) $$ Hcc with ⟨Hcc, #Hclb⟩
  have hp : DirOk d' W (R ++ r.got) ∧
      (1 ≤ max x (if r = .eof ∨ r = .err .sys then 1 else 0) → d'.dead) ∧
      (1 ≤ max c (if r = .err .closed then 1 else 0) → st.closed = true) := by
    refine ⟨Hok', fun hx => ?_, fun hc => ?_⟩
    · by_cases hr : r = .eof ∨ r = .err .sys
      · exact readOutcome_dead_of Hro hr
      · simp only [hr, ↓reduceIte, Nat.max_zero] at hx
        exact (readOutcome_dead (Hok.2.1 hx) Hro).1
    · by_cases hr : r = .err .closed
      · subst hr; exact readOutcome_closed_of Hro
      · simp only [hr, ↓reduceIte, Nat.max_zero] at hc
        exact Hok.2.2 hc
  imod Hcl $$ Hend Hdir HwQ Hr0 Hrd Hx Hcc %hp with -
  imodintro
  isplitl [Hr]
  · isplitl [Hr]
    · iexists γ, Pd, Pa
      iframe He Hreg Hai Hm Hr Hlb'
      ipureintro; exact hP
    · rw [← hP]; iexact Hpp'
  isplitr
  · ipureintro; exact ⟨st, d, d', Hro⟩
  · iintro %hr
    unfold readDead
    iexists γ
    iframe He
    by_cases hc : r = .err .closed
    · iright
      iapply monoNatLbOwn_le 1 ?_ $$ Hclb
      rw [ite_eq_left hc]; exact Nat.le_max_right _ _
    · ileft
      iapply monoNatLbOwn_le 1 ?_ $$ Hxlb
      have hr' : r = .eof ∨ r = .err .sys := by
        rcases hr with h | h | h
        · exact .inl h
        · exact .inr h
        · exact absurd h hc
      rw [ite_eq_left hr']; exact Nat.le_max_right _ _

end access

end Net
end Perennial
