/-
Proof of `Spec/.../mvcc/watchableStore__addVictim.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__addVictim

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A non-blocking send on a bag channel of trivial payloads: never closed. -/
theorem mvcc.bag_nb_send_au {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    (γ : ChanNames) (ch : Loc) (v : V) (Φ : IProp GF) :
    ⊢ isChanBag γ ch (fun _ : V => iprop(True)) -∗ Φ -∗ nonblockingSendAuInner γ v Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef nonblockingSendAuInner
  iintro ⟨#Hch, #Hinv⟩ HΦ
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold chanBagInv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iexists s
  iframe Hoc0
  rcases s with buff | _ | _ | _ | _ | _ | _
  all_goals dsimp only
  case Buffered =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Hi] with -
    · inext; iexists .Buffered (buff ++ [v])
      dsimp only
      iframe Hoc
      iapply BigSepL.bigSepL_append.2
      iframe Hi
      iapply BigSepL.bigSepL_singleton.2
      itrivial
    imodintro
    iexact HΦ
  case RcvPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists .SndCommit v; iframe
    imodintro
    iexact HΦ
  all_goals first | itrivial | (iexfalso; iexact Hi)

theorem mvcc.watchableStore.addVictim.wp_proof :
    mvcc.watchableStore.addVictim.spec (GF := GF) (hG := hG) := by
  intro s st γ vs vbs wb dq Mw
  wp_start as ⟨#Hws, Hvf, Hvs, Hcap, Hwb⟩
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  (try wp_auto)
  wp_apply wp_map_len_lt $$ [$Hwb] as ⟨Hwb, %Hlt⟩
  have hsz : (W64 (Mw.size : Int) = W64 0) ↔ Mw.size = 0 := by
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp at this; omega
    · intro h; rw [h]; rfl
  wp_if_destruct
  · have h0 : Mw.size = 0 := hsz.1 Hif
    (try wp_auto)
    iapply HΦ
    iframe Hwb
    iexists vs
    rw [if_pos h0]
    iframe
  have h0 : ¬ Mw.size = 0 := fun h => Hif (hsz.2 h)
  (try wp_auto)
  wp_apply wp_slice_literal (l := [wb])
  isplitr
  · ipureintro; rfl
  iintro %zsl ⟨Hz, Hzcap⟩
  wp_auto
  wp_apply wp_slice_append $$ [$Hvs $Hcap $Hz] as %vs' ⟨Hvs, Hcap, -⟩
  (try wp_auto)
  wp_bind (App (Val (GoInstruction SelectStmt)) _)
  ihave #Hvch := is_bag_is_chan γv vc _ $$ Hvcb
  iapply chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.nonblockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, vc, γv, (zero_val Unit)
      isplit
      · ipureintro; exact ⟨rfl, rfl⟩
      isplit
      · iexact Hvch
      unfold nonblockingSendAu
      isplit
      · iapply mvcc.bag_nb_send_au γv vc (zero_val Unit) _ $$ Hvcb
        wp_auto
        iapply HΦ
        iframe Hwb
        iexists vs'
        rw [if_neg h0]
        iframe
      · itrivial
    · iapply BigAndL.bigAndL_nil.2
      itrivial
  · wp_auto
    iapply HΦ
    iframe Hwb
    iexists vs'
    rw [if_neg h0]
    iframe

end proof

end EtcdGrove
end Perennial
