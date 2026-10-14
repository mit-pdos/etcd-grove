/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/runSTM.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.runSTM
public import Perennial.Golang.Theory.Chan.Idioms.Bag

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

instance runSTM_stmResponse_countable [FfiSyntax] : Pos.Countable stmResponse :=
  .ofInjective (fun r => Pos.Countable.encode (r.resp', r.err'))
    (by rintro ⟨a, b⟩ ⟨a', b'⟩ h; have h := Pos.encode_inj h; simp_all)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem runSTM.wp_proof :
    runSTM.spec (GF := GF) (hG := hG) := by
  intro lvl pfx p apply Q lo
  wp_start as ⟨#Hm, Hst, #Hap, #Hlo⟩
  ihave #Hm' := Hm
  iunfold stmMethods at Hm'
  icases Hm' with ⟨#HGet, #HPut, #HRev, #HDel, #HCommit, #HReset⟩
  ihave #Hap' := Hap
  iunfold applySpec at Hap'
  simp only [stmIface]
  wp_auto
  wp_apply chan.wp_make2 (V := stmResponse) $$ [] as %ch %γ ⟨#His, -, Hown⟩
  · ipureintro; decide
  imod start_bag (fun r : stmResponse => stmResult (GF := GF) pfx lvl lo Q r.resp' r.err') _ ch γ
    trivial $$ His Hown with #Hch
  ipersist outc
  wp_apply wp_fork $$ [Hst s apply]
  · wp_auto
    wp_apply wp_with_defer_recover as %defer %pnc defer pnc
    ihave IH : iprop(∃ o : stmResponse, "out" ∷ out_ptr ↦ o ∗ "Hst" ∷ stmStale lvl pfx p) $$ [out Hst]
    · iexists _; simp only [named]; iframe
    wp_for IH
    (try rw [if_pos (decide_eq_true rfl)])
    (try wp_auto)
    wp_apply HReset $$ [$Hst] as Hst
    ihave #Happ := Hap' $$ %lvl %p %STMSt.empty Hm
    wp_apply Happ $$ [$Hst] as %r Hr
    iunfold stmRet at Hr
    icases Hr with (⟨%err, %Hr, %st', Hst, %Herr⟩ | %Hab)
    rotate_left
    · -- the attempt aborted (`panic(stmError{err})`): the panic leaves the loop and reaches the
      -- `Catch`, whose deferred literal recovers it and sends `(nil, err)`
      obtain ⟨e, Hne, rfl⟩ := Hab
      unfold stmAbort
      wp_auto
      wp_for_post
      wp_apply wp_recoverPanic $$ [$pnc] as pnc
      wp_apply wp_bag_send (P := fun r : stmResponse => stmResult (GF := GF) pfx lvl lo Q r.resp' r.err')
        $$ [$Hch]
      · unfold stmResult; ileft; ipureintro; exact Hne
      itrivial
    subst Hr
    wp_auto
    cases err with
    | ok e =>
      wp_auto
      wp_for_post
      wp_apply wp_bag_send (P := fun r : stmResponse => stmResult (GF := GF) pfx lvl lo Q r.resp' r.err')
        $$ [$Hch]
      · unfold stmResult; ileft; ipureintro; simp
      wp_apply wp_recoverPanic $$ [$pnc] as pnc
      itrivial
    | nil =>
      wp_auto
      wp_apply HCommit $$ [$Hst $Hlo] as %r Hr
      iunfold stmRet at Hr
      icases Hr with (⟨%resp, %Hr, Hst, Hres⟩ | %Hab)
      rotate_left
      · -- the commit aborted: as above
        obtain ⟨e, Hne, rfl⟩ := Hab
        unfold stmAbort
        wp_auto
        wp_for_post
        wp_apply wp_recoverPanic $$ [$pnc] as pnc
        wp_apply wp_bag_send (P := fun r : stmResponse => stmResult (GF := GF) pfx lvl lo Q r.resp' r.err')
          $$ [$Hch]
        · unfold stmResult; ileft; ipureintro; exact Hne
        itrivial
      subst Hr
      wp_auto
      icases Hres with (%Hnull | ⟨%Hnn, #Hout⟩)
      · subst Hnull
        wp_auto
        wp_for_post
        iframe
        iexists _
        simp only [named]
        iframe
      · (try wp_auto)
        (try rw [decide_eq_false Hnn])
        (try wp_auto)
        wp_for_post
        wp_apply wp_bag_send (P := fun r : stmResponse => stmResult (GF := GF) pfx lvl lo Q r.resp' r.err')
          $$ [$Hch]
        · unfold stmResult
          iright
          isplitr
          · ipureintro; rfl
          iexists st'
          iframe #
          ipureintro; exact Herr rfl
        wp_apply wp_recoverPanic $$ [$pnc] as pnc
        itrivial
  wp_apply wp_bag_receive (t := stmResponse.ty) γ ch
    (fun r : stmResponse => stmResult (GF := GF) pfx lvl lo Q r.resp' r.err') $$ [$Hch] as %r #Hr
  iapply HΦ
  iexact Hr

end proof

end concurrency
end EtcdGrove
end Perennial
