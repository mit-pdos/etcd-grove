/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/NewSTM.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.NewSTM
public import Spec.go_etcd_io.etcd.client.v3.Client__Ctx
public import Spec.go_etcd_io.etcd.client.v3.concurrency.mkSTM
public import Spec.go_etcd_io.etcd.client.v3.concurrency.runSTM

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem NewSTM.wp_proof (hCtx : Client.Ctx.spec (GF := GF) (hG := hG))
    (hMk : mkSTM.spec (GF := GF) (hG := hG)) (hRun : runSTM.spec (GF := GF) (hG := hG)) :
    NewSTM.spec (GF := GF) (hG := hG) := by
  intro c pfx apply Q sl os lo
  wp_start as ⟨#Hcl, #Hap, #Hopts, #Hlo, %Hpre⟩
  ihave #Hcl' := Hcl
  iunfold isEtcdSTMClient at Hcl'
  icases Hcl' with ⟨%kv, %cctx, %ccs, #Hkv, #Htxn, #Hrtxn, #Hcf, #Hcc⟩
  wp_auto
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply hCtx c (GoInterface.ok cctx) $$ [$Hcv $Hcf]
  (try wp_auto)
  -- the options, in order
  ihave #Hopts' := Hopts
  iunfold stmOptsAt at Hopts'
  icases Hopts' with ⟨%fs, #Hfs, %Hlen, #Hf⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hfs
  ihave Hown : stmOptionsOwn (GF := GF) «$r0_ptr» STMOpts.init $$ [«$r0»]
  · unfold stmOptionsOwn
    iexists cctx, ccs, slice.nil
    iframe
    iframe #
    simp only [STMOpts.init]
    isplitl
    · iapply ownSlice_nil
    iapply ownSliceCap_nil
  ihave IH : iprop(∃ (n : w64) (f0 : GoFunc),
      "i" ∷ i_ptr ↦ n ∗ "Hop" ∷ stmOptionsOwn «$r0_ptr» (stmOptsFold (os.take (sint.nat n))
        STMOpts.init) ∗ "f" ∷ f_ptr ↦ f0 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (fs.length : Int)⌝) $$ [i Hown f]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < fs.length := by word
    obtain ⟨f, Hfi⟩ : ∃ f, fs[sint.nat n]? = some f := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨g, Hgi⟩ : ∃ g, os[sint.nat n]? = some g :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) fs DFrac.discard f Hn.1 $$ [Hfs] as -
    · iframe #; ipureintro; exact Hfi
    ihave #Hg := Hf $$ %(sint.nat n) %f %g %Hfi %Hgi
    unfold stmOptSpec
    wp_apply Hg $$ [$Hop] as Hop
    wp_for_post
    iframe
    iexists n + W64 1, f
    simp only [named]
    iframe
    isplitl [Hop]
    · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, stmOptsFold_take_succ os _ _ g Hgi]
      iexact Hop
    ipureintro; constructor <;> word
  have Hge : sint.nat n = os.length := by rw [← Hlen]; word
  rw [Hge, List.take_length]
  generalize hO : stmOptsFold os STMOpts.init = O at Hpre ⊢
  unfold stmOptionsOwn
  icases Hop with ⟨%octx, %ocs, %psl, Hr, Hpsl, -, #Hoctx⟩
  ipersist Hr
  ipersist Hpsl
  ipersist opts
  ihave #Hr2 := Hr
  iStructNamed Hr2
  wp_auto
  ihave %Hplen := ownSlice_len _ _ _ $$ Hpsl
  wp_if_destruct
  · -- no prefetch list
    wp_apply hMk c pfx «$r0_ptr» _ octx ocs $$ [$Hpkg $Hcl $Hr $Hoctx] as %stmv ⟨%sp, %Hs, #Hms, Hstale⟩
    · ipureintro; exact ⟨rfl, Hpre.1⟩
    subst Hs
    wp_apply hRun O.iso pfx sp apply Q lo $$ [$Hpkg $Hms $Hstale $Hap $Hlo] as %resp %err #Hres
    iapply HΦ
    iexact Hres
  · -- a prefetch list: `apply` wrapped in a closure that gets the keys first
    ipersist f
    wp_apply hMk c pfx «$r0_ptr» _ octx ocs $$ [$Hpkg $Hcl $Hr $Hoctx] as %stmv ⟨%sp, %Hs, #Hms, Hstale⟩
    · ipureintro; exact ⟨rfl, Hpre.1⟩
    subst Hs
    wp_apply hRun O.iso pfx sp _ Q lo $$ [$Hpkg $Hms $Hstale $Hlo] as %resp %err #Hres
    · unfold applySpec
      imodintro
      iintro %lvl %p %st #Hm
      wp_start_folded as Hst
      ihave #Hm' := Hm
      iunfold stmMethods at Hm'
      icases Hm' with ⟨#HGet, -⟩
      ihave #Hap1 := Hap $$ %lvl %p
      ihave #HGet1 := HGet $$ %st %psl %O.prefetch
      simp only [stmIface]
      wp_auto
      wp_apply HGet1 $$ [$Hst $Hpsl] as %r Hr
      · ipureintro; exact Hpre.2
      iunfold stmRet at Hr
      icases Hr with (⟨%v, %Hv, %st', Hst, -⟩ | %Hab)
      rotate_left
      · -- the prefetch aborted: so does the closure
        obtain ⟨err, Hne, rfl⟩ := Hab
        unfold stmAbort
        wp_auto
        iapply HΦ
        iapply stmRet_abort _ Hne
      subst Hv
      wp_auto
      ihave #Hap3 := Hap1 $$ %st' Hm
      wp_apply Hap3 $$ [$Hst] as %r' Hres
      iunfold stmRet at Hres
      icases Hres with (⟨%err, %Herr, Hres⟩ | %Hab)
      rotate_left
      · obtain ⟨err, Hne, rfl⟩ := Hab
        unfold stmAbort
        wp_auto
        iapply HΦ
        iapply stmRet_abort _ Hne
      subst Herr
      wp_auto
      iapply HΦ
      iapply stmRet_ret
      iexact Hres
    iapply HΦ
    iexact Hres


end proof

end concurrency
end EtcdGrove
end Perennial
