/-
**A `channelContext` is a context the client's watch takes** (`watchCtx`; 2026-11-04, Q1 (b) of
`notes/k8s-compactor-plan.md`: Kubernetes' compactor watches its key under
`wait.ContextForChannel(stopCh)`). Lean-first.

`channelContext{stopCh: sc}`'s `Done()` returns `sc` and its `Err()` is `nil` while `sc` is open,
`context.Canceled` once it is closed (`Spec/k8s_io/apimachinery/pkg/util/wait/`). Its descriptor
here is `cdesc ⟨γdn, γi.doneGn⟩ True`: its closed flag is the broadcast channel's own done flag
(`γi`, its internal names, set exactly when `sc` is closed), and its Done cell `γdn` a fresh name
fixed to `sc`. `isContextDone` wants the channel's proposition to give the closed flag:
`broadcast_closed_flag` restates the channel's invariant with the flag added to it (the invariant
already holds the flag once the channel is closed).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ChanCtx
public import Proof.context.WatchCtx
public import Spec.k8s_io.apimachinery.pkg.util.wait.channelContext__Done

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

/-- **A broadcast channel's proposition can carry its done flag**: once the channel is closed, its
invariant holds the flag (discarded `true`), so the invariant with `Q ∗ flag` for `Q` is the same. -/
theorem broadcast_closed_flag (sc : GoChan) (γs : ChanNames) (γi : BroadcastInternalNames)
    (Q : IProp GF) :
    isBroadcastChanInternal sc γs γi Q ⊢
      isBroadcastChanInternal sc γs γi iprop(Q ∗ dghostVar γi.doneGn .discard true) := by
  unfold isBroadcastChanInternal
  iintro ⟨#Hch, #Hinv⟩
  isplitr
  · iexact Hch
  iapply inv_alter $$ Hinv
  inext
  imodintro
  iintro Hb
  unfold broadcastInv
  icases Hb with ⟨%st, Hc, Hs⟩
  isplitl [Hc Hs]
  · iexists st
    iframe Hc
    rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
    all_goals dsimp only
    all_goals first
      | iexact Hs
      | (icases Hs with ⟨#HQ, #Hd⟩
         isplitl []
         · imodintro; iframe HQ Hd
         · iexact Hd)
  · iintro Hb
    icases Hb with ⟨%st, Hc, Hs⟩
    iexists st
    iframe Hc
    rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
    all_goals dsimp only
    all_goals first
      | iexact Hs
      | (icases Hs with ⟨#⟨HQ, -⟩, #Hd⟩
         isplitl []
         · imodintro; iexact HQ
         · iexact Hd)

/-- **`context.Canceled`'s value is a context error** (`isCtxErr`, not `nil`): from `context`'s
package fact. -/
theorem isCtxErr_of_canceled (e : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗
      globalAddr _root_.Perennial.context.Canceled ↦□ e ⊢
      ⌜e ≠ GoInterface.nil⌝ ∗ _root_.Perennial.context.isCtxErr e := by
  iintro ⟨#Pctx, #He⟩
  ihave Hci : (_root_.Perennial.context.isInit : IProp GF) $$ []
  · iapply _root_.Perennial.context.isInit_access $$ Pctx
  iNamed Hci
  icases HCanceledCell with ⟨%x, #Hx, #Hcell⟩
  icombine He Hx gives %Heq
  subst Heq
  isplitr
  · ipureintro; nofun
  unfold _root_.Perennial.context.isCtxErr
  ileft
  iframe Hx
  iexists x
  iframe Hcell
  ipureintro; rfl

/-- **A `channelContext` over a broadcast channel is a context the watch takes** (see the file
header), at a fresh Done cell; the channel's proposition `True` (a stop channel's). -/
theorem chanCtx_watch (wp_Done : wait.channelContext.Done.spec (GF := GF) (hG := hG))
    (wp_Err : wait.channelContext.Err.spec (GF := GF) (hG := hG))
    (wp_Value : wait.channelContext.Value.spec (GF := GF) (hG := hG))
    (sc : GoChan) (γs : ChanNames) (γi : BroadcastInternalNames) :
    isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.wait ∗
      isBroadcastChanInternal sc γs γi iprop(True) ⊢ |==> ∃ γdn : GName,
      context.watchCtx (chanCtxVal sc)
        (_root_.Perennial.context.cdesc ⟨γdn, γi.doneGn⟩ iprop(True)) := by
  iintro ⟨#Pw, #Hint⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  imod dghostVar_alloc (GF := GF) (some sc : Option GoChan) with ⟨%γdn, Hd⟩
  imod dghostVar_persist $$ Hd with #Hd
  iexists γdn
  ihave #Hint' := broadcast_closed_flag sc γs γi iprop(True) $$ Hint
  ihave #Hbc : ownBroadcastChan sc γs
      iprop(iprop(True) ∗ _root_.Perennial.context.ContextClosed
        (⟨γdn, γi.doneGn⟩ : _root_.Perennial.context.ContextNames)) .Unknown $$ []
  · rw [ownBroadcastChan_unseal]
    unfold ownBroadcastChanDef
    iexists γi
    isplitl []
    · unfold _root_.Perennial.context.ContextClosed
      iexact Hint'
    · itrivial
  ihave #HD := _root_.Perennial.context.isContextDone_of_broadcast ⟨γdn, γi.doneGn⟩ iprop(True)
    sc γs $$ Hd Hbc
  ihave #HoC := chanCtx_outgoingCtxOkC wp_Value sc $$ Pw
  imodintro
  unfold context.watchCtx
  isplitr
  · iintro !> %Φ - HΦ
    iapply (wp_Done sc) $$ [Pw]
    · iexact Pw
    inext
    iintro -
    iapply HΦ $$ HD
  isplitr
  · iintro %cl !> %Φ Hcl HΦ
    iapply (wp_Err sc γs γi iprop(True) cl) $$ [Hcl]
    · iframe Pw Hint
      rcases cl with _ | _ | _ <;> dsimp only
      · itrivial
      · iunfold _root_.Perennial.context.ContextClosed at Hcl; iexact Hcl
      · itrivial
    inext
    iintro %err Hr
    icases Hr with (%Hn | ⟨#Hc, #Hdn⟩)
    · obtain ⟨rfl, hcl⟩ := Hn
      iapply HΦ
      · rcases cl with _ | _ | _ <;> dsimp only
        · simp only [↓reduceIte]; itrivial
        · exact absurd rfl hcl
        · simp only [↓reduceIte]; itrivial
      · simp only [↓reduceIte]; itrivial
    · ihave ⟨%Hne, #Hce⟩ := isCtxErr_of_canceled err $$ [Pctx Hc]
      · iframe Pctx Hc
      iapply HΦ
      · rcases cl with _ | _ | _ <;> dsimp only
        · rw [ite_eq_right_of_eq_false _ _ (eq_false Hne)]
          isplitl []
          · imodintro; itrivial
          · iunfold _root_.Perennial.context.ContextClosed; iexact Hdn
        · ipureintro; exact Hne
        · rw [ite_eq_right_of_eq_false _ _ (eq_false Hne)]
          isplitl []
          · imodintro; itrivial
          · iunfold _root_.Perennial.context.ContextClosed; iexact Hdn
      · rw [ite_eq_right_of_eq_false _ _ (eq_false Hne)]; iexact Hce
  · iexact HoC

end proofs

end EtcdGrove
end Perennial
