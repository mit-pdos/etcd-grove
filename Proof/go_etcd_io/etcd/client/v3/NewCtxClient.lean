/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewCtxClient.lean` (PR etcd#22658).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewCtxClient
public import Spec.go_uber_org.zap.NewNop
public import Proof.go_etcd_io.etcd.client.v3.InvCmpTypes

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem NewCtxClient.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG)) :
    NewCtxClient.spec (GF := GF) (hG := hG) := by
  intro ctx cs optsSl opts
  wp_start as ⟨#Hctx, #Hsl, #Hopts⟩
  ihave #HctxPkg : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #HsyncPkg : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #HzapPkg : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #HatomPkg : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_apply context.wp_WithCancel_any ctx cs $$ [$HctxPkg $Hctx]
    as %ctx' %γ' %cancelFn ⟨#Hcancel, #Hctx'⟩
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨«$r0», %Hcnn⟩
  iStructNamedPrefix «$r0» "C"
  ihave Hlgown : sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger)
      (clientLgAddr «$r0_ptr») (DFrac.own 1) null $$ [Clg]
  · rw [sync.atomic.ownPointer_unseal]; unfold sync.atomic.ownPointerDef; iexact Clg
  imod (sync.init_RWMutex (fun _ => iprop(True)) «$v2_ptr» (E := ⊤)) $$ [] «$v2» with Hslots
  · inext; itrivial
  icases sync.ownRWMutex_slots_guard _ _ $$ Hslots with ⟨-, #Hguard⟩
  ipersist CepMu
  ipersist Cresolver
  ipersist Cctx
  ipersist Ccancel
  ihave IH : iprop(∃ (n : w64) (lg0 : Loc) (opt0 : GoFunc),
      "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ «$r0_ptr» ∗ "opt" ∷ opt_ptr ↦ opt0 ∗
      "Hlgown" ∷ sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger)
        (clientLgAddr «$r0_ptr») (DFrac.own 1) lg0 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (opts.length : Int)⌝) $$ [i c opt Hlgown]
  · iexists W64 0, null, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < opts.length := by word
    obtain ⟨f, Hfi⟩ : ∃ f, opts[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z optsSl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index optsSl (sint.Z n) opts DFrac.discard f Hn.1 $$ [Hsl] as -
    · iframe #; ipureintro; exact Hfi
    ihave #Hf := Hopts $$ %(sint.nat n) %f %Hfi
    iunfold ctxClientOptOk at Hf
    ihave #Hf := Hf $$ %«$r0_ptr» %lg0
    wp_apply Hf $$ [$Hpkg $Hlgown] as ⟨%lg1, Hlgown⟩
    wp_for_post
    iframe
    iexists n + W64 1, lg1, f
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  · wp_bind (App (Val #(methods _ _ _)) (Val #()))
    iapply (sync.atomic.Pointer.wp_Load (T' := go_uber_org.zap.Logger) go_uber_org.zap.Logger.ty
      (clientLgAddr «$r0_ptr») (DFrac.own 1))
    · iexact HatomPkg
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists lg0
    iframe Hlgown
    iintro Hlgown
    imod Hmask with -
    by_cases Hlg0 : lg0 = null
    · subst Hlg0
      imodintro
      wp_auto
      wp_apply wp_NewNop $$ [$HzapPkg] as %nopLg %Hnopnn
      wp_bind (App (Val #(methods _ _ _)) (Val #nopLg))
      iapply (sync.atomic.Pointer.wp_Store (T' := go_uber_org.zap.Logger) go_uber_org.zap.Logger.ty
        (clientLgAddr «$r0_ptr») nopLg)
      · iexact HatomPkg
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iexists null
      iframe Hlgown
      iintro Hlgown
      imod Hmask with -
      imod (inv_alloc clientLgN ⊤ iprop(∃ lg : Loc,
          sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger) (clientLgAddr «$r0_ptr»)
            (DFrac.own 1) lg ∗ ⌜lg ≠ null⌝)) $$ [Hlgown] with #HcLg
      · inext; iexists nopLg; iframe; ipureintro; exact Hnopnn
      imodintro
      wp_auto
      iapply HΦ
      isplitr
      · ipureintro; exact Hcnn
      isplitl []
      · iunfold isClientLogger; iexact HcLg
      isplitl []
      · iexists «$v2_ptr»; iframe CepMu Hguard
      iframe Cendpoints Cresolver
      iexists ctx', γ', cancelFn
      iframe Cctx Ccancel Hcancel Hctx'
    · imod (inv_alloc clientLgN ⊤ iprop(∃ lg : Loc,
          sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger) (clientLgAddr «$r0_ptr»)
            (DFrac.own 1) lg ∗ ⌜lg ≠ null⌝)) $$ [Hlgown] with #HcLg
      · inext; iexists lg0; iframe; ipureintro; exact Hlg0
      imodintro
      wp_auto
      rw [decide_eq_false Hlg0]
      wp_auto
      iapply HΦ
      isplitr
      · ipureintro; exact Hcnn
      isplitl []
      · iunfold isClientLogger; iexact HcLg
      isplitl []
      · iexists «$v2_ptr»; iframe CepMu Hguard
      iframe Cendpoints Cresolver
      iexists ctx', γ', cancelFn
      iframe Cctx Ccancel Hcancel Hctx'

end proof

end EtcdGrove
end Perennial
