/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/FutBase.lean (241f27e).
-/
/-
Stage 2 (API): `init` and `respond` promoted through `*verifyFuture` and `*leadershipTransferFuture`
(as `deferError.init.spec`/`deferError.respond.spec` through `*logFuture`; same proofs).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

namespace github_com.hashicorp.raft.futProof

theorem wp_vf_init (f : Loc) (Q : GoInterface → IProp GF) (ch0 : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     (f.[verifyFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch0 }}
    (App (Val (f @!! go.GoType.PointerType verifyFuture.ty @!! go!"init")) (Val #()))
  {{ RET #(); ∃ (ch : Loc) (γe : SpscNames), ⌜ch ≠ chan.nil⌝ ∗
      (f.[verifyFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch ∗
      isSpsc (V := GoInterface) γe ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) ∗
      spscProducer γe ([] : List GoInterface) ∗ spscConsumer γe ([] : List GoInterface) }} := by
  wp_start as Hch
  wp_method_call
  wp_call
  iapply wp_fupd
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ch %γc ⟨#Hisch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave %Hnn := isChan_not_null (ch := ch) (γ := γc) (V := GoInterface) $$ Hisch
  imod start_spsc ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) γc $$ Hisch [Hown]
    with ⟨%γe, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hown
  imodintro
  iapply HΦ
  iexists ch, γe
  iframe
  iframe #
  ipureintro; exact Hnn

theorem wp_vf_respond (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     ((deferResp (f.[verifyFuture, go!"deferError"]) Q ∗ Q err) ∨
      deferDone (f.[verifyFuture, go!"deferError"])) }}
    (App (Val (f @!! go.GoType.PointerType verifyFuture.ty @!! go!"respond")) (Val #err))
  {{ RET #(); deferDone (f.[verifyFuture, go!"deferError"]) }} := by
  wp_start as Hpre
  wp_method_call
  wp_call
  unfold deferDone
  icases Hpre with (⟨Hresp, HQ⟩ | Hdone)
  · unfold deferResp
    icases Hresp with ⟨%ch, #Hch, (%Hnil | ⟨%γe, %Hne, #Hspsc, Hprod, Hr⟩)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
      wp_auto
      wp_apply (wp_spsc_send γe ch _ _ [] err) $$ [$Hspsc $Hprod HQ] as Hprod
      · iframe; ipureintro; rfl
      wp_apply (wp_spsc_close γe ch _ _ ([] ++ [err])) $$ [$Hspsc $Hprod]
      · ipureintro; simp
      iapply HΦ
      iexists ch; iframe #; iright; iframe
  · icases Hdone with ⟨%ch, #Hch, (%Hnil | Hr)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      wp_if_destruct
      · iapply HΦ
        iexists _; iframe #; ileft; ipureintro; rfl
      · iapply HΦ
        iexists ch; iframe #; iright; iframe

theorem wp_ltf_init (f : Loc) (Q : GoInterface → IProp GF) (ch0 : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     (f.[leadershipTransferFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch0 }}
    (App (Val (f @!! go.GoType.PointerType leadershipTransferFuture.ty @!! go!"init")) (Val #()))
  {{ RET #(); ∃ (ch : Loc) (γe : SpscNames), ⌜ch ≠ chan.nil⌝ ∗
      (f.[leadershipTransferFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch ∗
      isSpsc (V := GoInterface) γe ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) ∗
      spscProducer γe ([] : List GoInterface) ∗ spscConsumer γe ([] : List GoInterface) }} := by
  wp_start as Hch
  wp_method_call
  wp_call
  iapply wp_fupd
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ch %γc ⟨#Hisch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave %Hnn := isChan_not_null (ch := ch) (γ := γc) (V := GoInterface) $$ Hisch
  imod start_spsc ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) γc $$ Hisch [Hown]
    with ⟨%γe, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hown
  imodintro
  iapply HΦ
  iexists ch, γe
  iframe
  iframe #
  ipureintro; exact Hnn

theorem wp_ltf_respond (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     ((deferResp (f.[leadershipTransferFuture, go!"deferError"]) Q ∗ Q err) ∨
      deferDone (f.[leadershipTransferFuture, go!"deferError"])) }}
    (App (Val (f @!! go.GoType.PointerType leadershipTransferFuture.ty @!! go!"respond")) (Val #err))
  {{ RET #(); deferDone (f.[leadershipTransferFuture, go!"deferError"]) }} := by
  wp_start as Hpre
  wp_method_call
  wp_call
  unfold deferDone
  icases Hpre with (⟨Hresp, HQ⟩ | Hdone)
  · unfold deferResp
    icases Hresp with ⟨%ch, #Hch, (%Hnil | ⟨%γe, %Hne, #Hspsc, Hprod, Hr⟩)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
      wp_auto
      wp_apply (wp_spsc_send γe ch _ _ [] err) $$ [$Hspsc $Hprod HQ] as Hprod
      · iframe; ipureintro; rfl
      wp_apply (wp_spsc_close γe ch _ _ ([] ++ [err])) $$ [$Hspsc $Hprod]
      · ipureintro; simp
      iapply HΦ
      iexists ch; iframe #; iright; iframe
  · icases Hdone with ⟨%ch, #Hch, (%Hnil | Hr)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      wp_if_destruct
      · iapply HΦ
        iexists _; iframe #; ileft; ipureintro; rfl
      · iapply HΦ
        iexists ch; iframe #; iright; iframe

/-- (stage 4) `init`/`respond` promoted through `*configurationsFuture` (`GetConfiguration`). -/
theorem wp_cf_init (f : Loc) (Q : GoInterface → IProp GF) (ch0 : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     (f.[configurationsFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch0 }}
    (App (Val (f @!! go.GoType.PointerType configurationsFuture.ty @!! go!"init")) (Val #()))
  {{ RET #(); ∃ (ch : Loc) (γe : SpscNames), ⌜ch ≠ chan.nil⌝ ∗
      (f.[configurationsFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch ∗
      isSpsc (V := GoInterface) γe ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) ∗
      spscProducer γe ([] : List GoInterface) ∗ spscConsumer γe ([] : List GoInterface) }} := by
  wp_start as Hch
  wp_method_call
  wp_call
  iapply wp_fupd
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ch %γc ⟨#Hisch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave %Hnn := isChan_not_null (ch := ch) (γ := γc) (V := GoInterface) $$ Hisch
  imod start_spsc ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) γc $$ Hisch [Hown]
    with ⟨%γe, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hown
  imodintro
  iapply HΦ
  iexists ch, γe
  iframe
  iframe #
  ipureintro; exact Hnn

theorem wp_cf_respond (f : Loc) (Q : GoInterface → IProp GF) (err : GoInterface) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     ((deferResp (f.[configurationsFuture, go!"deferError"]) Q ∗ Q err) ∨
      deferDone (f.[configurationsFuture, go!"deferError"])) }}
    (App (Val (f @!! go.GoType.PointerType configurationsFuture.ty @!! go!"respond")) (Val #err))
  {{ RET #(); deferDone (f.[configurationsFuture, go!"deferError"]) }} := by
  wp_start as Hpre
  wp_method_call
  wp_call
  unfold deferDone
  icases Hpre with (⟨Hresp, HQ⟩ | Hdone)
  · unfold deferResp
    icases Hresp with ⟨%ch, #Hch, (%Hnil | ⟨%γe, %Hne, #Hspsc, Hprod, Hr⟩)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      rw [show decide (ch = chan.nil) = false from decide_eq_false Hne]
      wp_auto
      wp_apply (wp_spsc_send γe ch _ _ [] err) $$ [$Hspsc $Hprod HQ] as Hprod
      · iframe; ipureintro; rfl
      wp_apply (wp_spsc_close γe ch _ _ ([] ++ [err])) $$ [$Hspsc $Hprod]
      · ipureintro; simp
      iapply HΦ
      iexists ch; iframe #; iright; iframe
  · icases Hdone with ⟨%ch, #Hch, (%Hnil | Hr)⟩
    · subst Hnil
      wp_auto
      iapply HΦ
      iexists _; iframe #; ileft; ipureintro; rfl
    · wp_auto
      wp_if_destruct
      · iapply HΦ
        iexists _; iframe #; ileft; ipureintro; rfl
      · iapply HΦ
        iexists ch; iframe #; iright; iframe

/-- (stage 4) `init` promoted through `*configurationChangeFuture` (twice: its `logFuture`'s `deferError`;
`requestConfigChange`). -/
theorem wp_ccf_init (f : Loc) (Q : GoInterface → IProp GF) (ch0 : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch0 }}
    (App (Val (f @!! go.GoType.PointerType configurationChangeFuture.ty @!! go!"init")) (Val #()))
  {{ RET #(); ∃ (ch : Loc) (γe : SpscNames), ⌜ch ≠ chan.nil⌝ ∗
      ((f.[configurationChangeFuture, go!"logFuture"]).[logFuture, go!"deferError"]).[deferError, go!"errCh"] ↦ ch ∗
      isSpsc (V := GoInterface) γe ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) ∗
      spscProducer γe ([] : List GoInterface) ∗ spscConsumer γe ([] : List GoInterface) }} := by
  wp_start as Hch
  wp_method_call
  wp_call
  wp_method_call
  wp_call
  iapply wp_fupd
  wp_auto
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ch %γc ⟨#Hisch, %Hcap, Hown⟩
  · ipureintro; decide
  ihave %Hnn := isChan_not_null (ch := ch) (γ := γc) (V := GoInterface) $$ Hisch
  imod start_spsc ch (fun n v => iprop(⌜n = 0⌝ ∗ Q v)) (fun sent => iprop(⌜sent ≠ []⌝)) γc $$ Hisch [Hown]
    with ⟨%γe, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hown
  imodintro
  iapply HΦ
  iexists ch, γe
  iframe
  iframe #
  ipureintro; exact Hnn

/-- A non-blocking send on a bag channel (`select` with a `default`): the bag's predicate goes in
when the send happens (as `bag_send_au`). -/
theorem bag_nb_send_au {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t]
    (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (v : V) (Φ : IProp GF) :
    ⊢ £ 1 -∗ isChanBag γ ch P -∗ P v -∗ ▷ Φ -∗ nonblockingSendAuInner γ v Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef nonblockingSendAuInner
  iintro Hlc1 ⟨#Hch, #Hinv⟩ HP HΦ
  iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold chanBagInv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hoc0
  rcases s with buff | _ | _ | _ | _ | _ | _
  all_goals dsimp only
  case Buffered =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Hi HP] with -
    · inext; iexists .Buffered (buff ++ [v])
      dsimp only
      iframe Hoc
      iapply BigSepL.bigSepL_append.2
      iframe Hi
      iapply BigSepL.bigSepL_singleton.2
      iexact HP
    imodintro
    iexact HΦ
  case RcvPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HP] with -
    · inext; iexists .SndCommit v; iframe
    imodintro
    iexact HΦ
  all_goals first | itrivial | (iexfalso; iexact Hi)

/-- A non-blocking receive on a bag channel (`select` with a `default`). -/
theorem bag_nb_recv_au {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (Φ : V → Bool → IProp GF) :
    ⊢ £ 1 -∗ isChanBag γ ch P -∗ (▷ ∀ v, P v -∗ Φ v true) -∗ nonblockingRecvAuInner γ V Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef nonblockingRecvAuInner
  iintro Hlc1 ⟨#Hch, #Hinv⟩ HΦ
  iapply ncfupd_of_fupd  -- (port) channel AUs are `|NC=…` now
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold chanBagInv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hoc0
  rcases s with (_ | ⟨v0, buff'⟩) | _ | v | _ | _ | _ | _
  all_goals dsimp only
  case Buffered.cons =>
    iintro Hoc
    icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨HP, Hi⟩
    imod Hmask with -
    imod Hclose $$ [Hoc Hi] with -
    · inext; iexists .Buffered buff'; iframe
    imodintro
    iapply HΦ $$ HP
  case SndPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists .RcvCommit; iframe
    imodintro
    iapply HΦ $$ Hi
  all_goals first | itrivial | (iexfalso; iexact Hi)

end github_com.hashicorp.raft.futProof

end proof

end Perennial
