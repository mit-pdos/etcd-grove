/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/initialize.lean (241f27e):
its lemmas. The proof itself is generated (`Init.lean`, from `etc/dsv/hraft.py`'s `special`).

To show raft's error variables pairwise distinct (`errVals`'s injectivity, `Base.lean`), the
initializer keeps three quarters of each new `errorString`'s field `s` (`exclS`); the last
quarter is made persistent, for `errors.newVar` and the `Error()` method.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ### Distinct `errors.New` results

Each `errors.New` result is a fresh `*errorString`. To show the error variables pairwise distinct
(`errVals`'s injectivity), the initializer keeps three quarters of each new string field
(`exclS`); a quarter is made persistent for the `Error()` method. -/

/-- Three quarters of the `s` field of the `errorString` at `x`. -/
def exclS (x : Loc) : IProp GF :=
  iprop(∃ m m' : GoString, x.[errors.errorString, go!"s"] ↦{DFrac.own (1 : Qp).half} m ∗
    x.[errors.errorString, go!"s"] ↦{DFrac.own (1 : Qp).half.half} m')

theorem string_pointsto_excl (l : Loc) (v w : GoString) (q : Qp) :
    l ↦{DFrac.own 1} v ∗ l ↦{DFrac.own q} w ⊢ (False : IProp GF) := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  rw [typedPointstoDef_heap, typedPointstoDef_heap]
  icombine H1 H2 gives % ⟨Hv, _⟩
  exact absurd (DFrac.valid_own_op Hv) (by simp)

theorem exclS_ne (x x' : Loc) : exclS (GF := GF) x ∗ exclS x' ⊢ ⌜x ≠ x'⌝ := by
  unfold exclS
  iintro ⟨⟨%m1, %m2, H1, H2⟩, ⟨%m3, %m4, H3, H4⟩⟩
  by_cases h : x = x'
  · subst h
    icases typedPointsto_half_combine _ _ _ 1 $$ [H1 H3] with ⟨-, H13⟩
    · iframe
    iexfalso
    iapply string_pointsto_excl $$ [H13 H2]
    iframe
  · ipureintro; exact h

theorem exclS_nodup (g : RaftErr → Loc) (l : List RaftErr) :
    ([∗list] c ∈ l, exclS (GF := GF) (g c)) ⊢ ⌜(l.map g).Nodup⌝ := by
  induction l with
  | nil => iintro -; ipureintro; simp
  | cons a l ih =>
    iintro ⟨Ha, Hl⟩
    ihave %Hnd := ih $$ Hl
    ihave %Hnot : ⌜∀ b ∈ l, g a ≠ g b⌝ $$ [Ha Hl]
    · iintro %b %hb
      icases BigSepL.bigSepL_mem_acc hb $$ Hl with ⟨Hb, -⟩
      iapply exclS_ne $$ [Ha Hb]
      iframe
    ipureintro
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun b hb h => Hnot b hb h.symm, Hnd⟩

theorem nodup_map_inj {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (e : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd e.symm (h.1 b hb)
    · exact absurd e (h.1 a ha)
    · exact ih h.2 ha hb

theorem bigSepL_all (F : RaftErr → IProp GF) :
    ([∗list] c ∈ RaftErr.all, F c) ⊣⊢ (F .leader ∗ F .notLeader ∗ F .notVoter ∗ F .leadershipLost ∗ F .abortedByRestore ∗ F .raftShutdown ∗ F .enqueueTimeout ∗ F .nothingNewToSnapshot ∗ F .unsupportedProtocol ∗ F .cantBootstrap ∗ F .leadershipTransferInProgress ∗ F .incompatibleLogStore ∗ F .shortBuffer ∗ F .transportShutdown ∗ F .pipelineShutdown ∗ F .logNotFound ∗ F .pipelineReplicationNotSupported ∗ emp) := .rfl

/-- `errors.New(msg)` (as `errors.wp_New_errorString`), also keeping `exclS` of the new
`errorString`. -/
theorem wp_New_excl [errors_sem : errors.Assumptions] (msg : GoString) :
    {{ (True : IProp GF) }}
      (App (Val (@! errors.New)) (Val #msg))
    {{ (x : Loc), RET #(interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x);
        x.[errors.errorString, go!"s"] ↦□ msg ∗ (□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
          WP (App (Val #(methods (go.GoType.PointerType errors.errorString.ty) go!"Error" #x))
            (Val #())) {{ Φ }}) ∗ exclS x }} := by
  wp_start
  wp_auto
  wp_alloc x as Hx
  iStructNamed Hx
  icases (typedPointsto_half_split _ _ 1).1 $$ s with ⟨s1, s2⟩
  icases (typedPointsto_half_split _ _ _).1 $$ s2 with ⟨s2, s3⟩
  ipersist s3
  wp_auto
  iapply HΦ
  iframe s3
  isplitr
  · imodintro
    iintro %Φ HΦ
    rw [method_unfold]
    wp_auto
    iexact HΦ
  · unfold exclS
    iexists msg, msg
    iframe

end proof

end github_com.hashicorp.raft

end Perennial
