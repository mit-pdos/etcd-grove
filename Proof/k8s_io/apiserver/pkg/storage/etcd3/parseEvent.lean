/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/parseEvent.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.parseEvent
public import Spec.go_etcd_io.etcd.api.v3.mvccpb.Event__IsCreate
public import Spec.go_etcd_io.etcd.api.v3.mvccpb.Event_EventType__StringPtr
public import Perennial.Proof.time.Link
public import Spec.fmt.ErrorfPlain

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem parseEvent.wp_proof
    (wp_IsCreate : mvccpb.Event.IsCreate.spec (GF := GF) (hG := hG))
    (wp_String : mvccpb.Event_EventType.StringPtr.spec (GF := GF) (hG := hG))
    (wp_ErrorfPlain : fmt.ErrorfPlain.spec (GF := GF) (hG := hG)) :
    parseEvent.spec (GF := GF) (hG := hG) := by
  intro p e ev o σ
  wp_start as ⟨⟨%Hp, %Hkvn⟩, #Hea, #Heis, #Hpk, #Hpko⟩
  ihave #Pmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb $$ []
  · iPkgInit
  ihave #Pti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Pf : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  iunfold EtcdGrove.eventAt at Hea
  icases Hea with ⟨%keySl0, #Hty, #Hkv, -, -, -⟩
  iunfold eventIs at Heis
  icases Heis with ⟨%Hev, #Hkvv⟩
  iunfold kvValAt at Hkvv
  icases Hkvv with ⟨%keySl, %valSl, #Hk, #Hks, #Hcr, #Hmr, -, #Hv, #Hvs, -⟩
  wp_auto
  wp_apply wp_IsCreate p e.kv e.typ ev.kv.createRev ev.kv.modRev $$ []
  · iframe #; ipureintro; exact ⟨Hp, Hkvn⟩
  have hIC : (e.typ = W32 0 ∧ ev.kv.createRev = ev.kv.modRev) ↔ v3rpc.evIsCreate ev := by
    unfold v3rpc.evIsCreate
    rw [Hev.1]
    cases ev.del <;> simp
  have hdel : decide (e.typ = W32 1) = ev.del := by
    rw [Hev.1]; cases ev.del <;> decide
  have hcr : decide (e.typ = W32 0 ∧ ev.kv.createRev = ev.kv.modRev) =
      decide (ev.del = false ∧ ev.kv.createRev = ev.kv.modRev) := by
    have := hIC; unfold v3rpc.evIsCreate at this; exact decide_eq_decide.mpr this
  wp_if_destruct
  · -- a create
    rename_i Hif
    have hc : v3rpc.evIsCreate ev := hIC.mp Hif
    wp_apply (wp_bytes_to_string keySl ev.kv.key DFrac.discard) $$ [$Hks] as -
    (try wp_auto)
    wp_apply wp_IsCreate p e.kv e.typ ev.kv.createRev ev.kv.modRev $$ []
    · iframe #; ipureintro; exact ⟨Hp, Hkvn⟩
    wp_apply _root_.Perennial.time.wp_Now as %t0 -
    (try wp_auto)
    ihave %Hpn : ⌜e.prevKv = null⌝ $$ [Hpko]
    · iunfold prevKvOk at Hpko
      split
      · icases Hpko with (%H | ⟨%r, ⟨%H, -⟩, -⟩)
        · ipureintro; exact H
        · exact absurd hc H
      · iexact Hpko
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe
      unfold kEvIs
      simp only [hdel, hcr]
      isplitr
      · ipureintro; simp
      isplitl
      · iexact Hvs
      · have hc' : ev.del = false ∧ ev.kv.createRev = ev.kv.modRev := hc
        simp only [hc', _root_.and_self, ↓reduceIte]
        ipureintro; trivial
    · exact absurd Hpn Hif
  · -- not a create
    rename_i Hif
    have hnc : ¬ v3rpc.evIsCreate ev := fun h => Hif (hIC.mpr h)
    wp_if_destruct
    · -- `PrevKv = nil`: the error
      (try wp_auto)
      wp_apply (wp_bytes_to_string keySl ev.kv.key DFrac.discard) $$ [$Hks] as -
      (try wp_auto)
      wp_apply wp_String (structFieldRef mvccpb.Event go!"Type" p) e.typ $$ [] as %s -
      · iframe #
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply (wp_ErrorfPlain _ _ _ _ (by refine ⟨_, rfl, ?_⟩; decide)) $$ [$Hsl]
        as %x ⟨-, %msg, -, -, #HE⟩
      · iframe #
        rw [show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl]
        try simp only [List.set_cons_succ, List.set_cons_zero]
        fmt_args_ok
      (try wp_auto)
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact ⟨by simp, Hif, hnc⟩
      iexists x
      isplitr
      · ipureintro; rfl
      unfold fmt.stringMethodSpec
      iintro !> %Φ' HΦ'
      iapply HE
      inext
      iapply HΦ'
    · -- `PrevKv` set: the key's record before
      ihave ⟨%r, %Hr, #Hpkv⟩ : ∃ r : KVRec, ⌜σ.at (sint.nat ev.kv.modRev - 1) !! ev.kv.key = some r⌝ ∗
          kvValAt e.prevKv (KVRec.toKv ev.kv.key r) $$ [Hpko]
      · iunfold prevKvOk at Hpko
        split
        · icases Hpko with (%H | ⟨%r, ⟨-, %H⟩, #Hk⟩)
          · exact absurd H Hif
          · iexists r; iframe #; ipureintro; exact H
        · icases Hpko with %H; exact absurd H Hif
      iunfold kvValAt at Hpkv
      icases Hpkv with ⟨%pkSl, %pvSl, -, -, -, -, -, #Hpv, #Hpvs, -⟩
      (try wp_auto)
      wp_apply (wp_bytes_to_string keySl ev.kv.key DFrac.discard) $$ [$Hks] as -
      (try wp_auto)
      wp_apply wp_IsCreate p e.kv e.typ ev.kv.createRev ev.kv.modRev $$ []
      · iframe #; ipureintro; exact ⟨Hp, Hkvn⟩
      wp_apply _root_.Perennial.time.wp_Now as %t0 -
      (try wp_auto)
      have Hpnn : e.prevKv ≠ null := Hif
      wp_if_destruct
      · exact absurd Hif Hpnn
      (try wp_auto)
      iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe
      unfold kEvIs
      simp only [hdel, hcr]
      isplitr
      · ipureintro; simp
      isplitl
      · iexact Hvs
      · have hc' : ¬ (ev.del = false ∧ ev.kv.createRev = ev.kv.modRev) := hnc
        simp only [hc', ↓reduceIte]
        iexists r
        isplitr
        · ipureintro; exact Hr
        · rw [show r.value = (KVRec.toKv ev.kv.key r).value from rfl]
          iexact Hpvs

end proof

end k8s
end EtcdGrove
end Perennial
