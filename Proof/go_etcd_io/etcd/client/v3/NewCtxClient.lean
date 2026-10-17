/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewCtxClient.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewCtxClient
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

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

theorem NewCtxClient.wp_proof (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG)) :
    NewCtxClient.spec (GF := GF) (hG := hG) := by
  intro parent s opts dsl
  wp_start as ⟨#Hctx, #Hopts, #Hdef⟩
  ihave #Hco := defaultCallOptsVar_callOptsAt dsl $$ Hdef
  iunfold defaultCallOptsVar at Hdef
  icases Hdef with ⟨#Hg, #Hvals, %Hlen⟩
  ihave #Hpctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_WithCancel_any parent s $$ [] as %ctx' %γ' %cancel ⟨#Hcancel, #Hctx'⟩
  · iframe #
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
  iStructNamedPrefix «$r0» "C"
  ihave Hlg0 : sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger)
      (clientLgAddr «$r0_ptr») (DFrac.own 1) null $$ [Clg]
  · rw [sync.atomic.ownPointer_unseal]; unfold sync.atomic.ownPointerDef; iexact Clg
  iunfold ctxClientOptsAt at Hopts
  icases Hopts with ⟨%fs, #Hfs, #Hfok⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hfs
  ihave IH : iprop(∃ (n : w64) (f0 : GoFunc) (lg : Loc),
      "i" ∷ i_ptr ↦ n ∗ "opt" ∷ opt_ptr ↦ f0 ∗
      "Hlg" ∷ sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger)
        (clientLgAddr «$r0_ptr») (DFrac.own 1) lg ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fs.length : Int)⌝) $$ [i opt Hlg0]
  · iexists W64 0, _, null
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < fs.length := by word
    obtain ⟨f, Hfi⟩ : ∃ f, fs[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z opts.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index opts (sint.Z n) fs DFrac.discard f Hn.1 $$ [Hfs] as -
    · iframe #; ipureintro; exact Hfi
    ihave #Hf := BigSepL.bigSepL_lookup (Φ := fun _ (g : GoFunc) => ctxClientOptOk (GF := GF) g)
      Hfi $$ Hfok
    iunfold ctxClientOptOk at Hf
    wp_apply Hf $$ %«$r0_ptr» %lg [$Hlg] as ⟨%lg', Hlg⟩
    wp_for_post
    iframe
    iexists n + W64 1, f, lg'
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  · wp_bind (App (Val #(methods _ _ _)) (Val #()))
    iapply (sync.atomic.Pointer.wp_Load (T' := go_uber_org.zap.Logger) go_uber_org.zap.Logger.ty
      (clientLgAddr «$r0_ptr») (DFrac.own 1))
    · iPkgInit
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists lg
    iframe Hlg
    iintro Hlg
    imod Hmask with -
    imodintro
    wp_auto
    wp_if_destruct
    · wp_apply wp_NewNop $$ [] as %nop %Hnop
      wp_bind (App (Val #(methods _ _ _)) (Val _))
      iapply (sync.atomic.Pointer.wp_Store (T' := go_uber_org.zap.Logger) go_uber_org.zap.Logger.ty
        (clientLgAddr «$r0_ptr») nop)
      · iPkgInit
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iexists null
      iframe Hlg
      iintro Hlg
      imod Hmask with -
      imodintro
      wp_auto
      iapply HΦ
      iframe
      iframe #
      ipureintro; exact ⟨Hnn, Hnop⟩
    · iapply HΦ
      iframe
      iframe #
      ipureintro; exact ⟨Hnn, Hif⟩

end proof

end EtcdGrove
end Perennial
