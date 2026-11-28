/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__Watch.lean` (k8s 7f-5b). The prepared key
(`prepareKey`: under the store's prefix, not empty, ending in `/` when recursive), the parsed
resource version (the versioner's `ParseResourceVersion`, `versionerOk`), and the watcher's `Watch`
over `watchContext(ctx)`, which is `WithRequireLeader(ctx)`: its result is a model context at the
caller's descriptor (`WithRequireLeader.isContext_of_post`) with grpc's outgoing metadata, its
`Err()` the caller's (`ctxErrClient`) and its APF initialization signal the caller's (the `Value`
transfer, at a key whose type is not grpc's `mdOutgoingKey`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__Watch
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__prepareKey
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__watchContext
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watcher__Watch
public import Proof.go_etcd_io.etcd.client.v3.WithRequireLeaderLaws
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

set_option maxHeartbeats 800000 in
theorem store.Watch.wp_proof
    (wp_prepareKey : store.prepareKey.spec (GF := GF) (hG := hG))
    (wp_watchContext : store.watchContext.spec (GF := GF) (hG := hG))
    (wp_WithRequireLeader : WithRequireLeader.spec (GF := GF) (hG := hG))
    (wp_wWatch : watcher.Watch.spec (GF := GF) (hG := hG)) :
    store.Watch.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ _ sp c W γk ci cd key opts k n sie sel emp Q HQok Hhist Hnr
  wp_start as ⟨Hlt, #Hst, #Hsw, %Hpre, #Hsie, #Hsel, #Hwl, #Hrs, #Hctx, #Hmd, #Hce, #Hk8, %Htb, Hra,
    #Hre⟩
  obtain ⟨hk, hkl, hrv, hn, hpn, hrt⟩ := Hpre
  ihave #Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨%Hsp, -, -, #Fvi, -, -, #Fpp, #Frp, -, -, -, -, -, -, #Hcon, -⟩
  iunfold contractOk at Hcon
  icases Hcon with ⟨-, -, #Hver, -, -, -, -⟩
  iunfold versionerOk at Hver
  icases Hver with ⟨-, -, -, #HParse⟩
  ihave #Hsw' := Hsw
  iunfold storeWatchOk at Hsw'
  icases Hsw' with ⟨%wp, %nf, %crv, %rse, #Fw, -⟩
  ihave #Hk8a := Hk8
  iunfold k8sctx.k8sCtxOk at Hk8a
  icases Hk8a with ⟨-, -, -, #Hsig, -⟩
  ihave #Pcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  imod Hra with #Hra
  wp_auto
  wp_apply wp_prepareKey sp c.resourcePrefix c.pathPrefix key opts.Recursive' $$ []
    as %pk %perr %Hpk
  · iframe #
  rw [hk] at Hpk
  obtain ⟨rfl, rfl⟩ := Hpk
  wp_auto
  wp_bind
  iapply HParse
  inext
  iintro %n' %err %hn'
  rw [hrv] at hn'
  obtain ⟨rfl, rfl⟩ := hn'
  wp_auto
  -- the require-leader context
  wp_apply (wp_watchContext sp (GoInterface.ok ci)
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      context.isContext ci cd ∗ metadata.outgoingCtxOkC ci ∗ ctxErrClient ci cd ∗
      context.valueAt ci flowcontrol.initSignalKeyAny (flowcontrol.initSignalRes (sem := sem)))
    (fun cv => iprop(∃ ci' : GoInterfaceOk, ⌜cv = GoInterface.ok ci'⌝ ∗
      context.isContext ci' cd ∗ metadata.outgoingCtxOkC ci' ∗ ctxErrClient ci' cd ∗
      context.valueAt ci' flowcontrol.initSignalKeyAny (flowcontrol.initSignalRes (sem := sem)))))
    $$ [] as %cv ⟨%ci', %Hcv, #Hctx', #Hmd', #Hce', #Hsig'⟩
  · intro Φ'
    iintro ⟨#Pcl', #Hc, #Hm, #He, #Hs⟩ HΦ'
    wp_apply (wp_WithRequireLeader ci cd) $$ []
      as %c' ⟨#HD, #HE, #HV, #HO, #HVal, -, #HDl, #HP, %Hty, -⟩
    · iframe #
      ileft
      iapply context.watchCtx_of_isContext $$ [$Hc $Hm]
    iapply HΦ'
    iexists c'
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply WithRequireLeader.isContext_of_post ci c' cd $$ [] Hc
      iframe #
      ipureintro; exact Hty
    isplitr
    · iexact HO
    isplitr
    · unfold ctxErrClient
      imodintro
      iintro %cl %Φ2 Hpre HΦ2
      iapply HE
      iapply He $$ Hpre HΦ2
    · unfold context.valueAt
      imodintro
      iintro %Φ2 HΦ2
      iapply HVal $$ %flowcontrol.initSignalKeyAny %(flowcontrol.initSignalRes (sem := sem))
        [] [] [] [HΦ2]
      · ipureintro
        intro k' hk'
        simp only [GoInterface.ok.injEq] at hk'
        subst hk'
        unfold google_golang_org.grpc.metadata.mdOutgoingKey.ty
          k8s_io.apiserver.pkg.util.flowcontrol.priorityAndFairnessKeyType.ty
        simp
      · iintro !> %Ψ - HΨ
        iapply Hs
        iexact HΨ
      · itrivial
      · inext; iexact HΦ2
  · iframe #
  subst Hcv
  have hpfx : c.pfx <+: c.pathPrefix ++ k := prepareKeyM_prefix _ _ _ _ _ hk
  have hne : c.pathPrefix ++ k ≠ [] := by
    intro h
    have hk0 : k = [] := (List.append_eq_nil_iff.1 h).2
    subst hk0
    unfold prepareKeyM at hk
    split at hk
    · cases hk
    split at hk
    · cases hk
    split at hk
    · cases hk
    rename_i h3
    split at hk
    · simp at hk
    · simp at hk
      exact h3 (Or.inl hk.2)
  have hsuf : opts.Recursive' = true → go!"/" <:+ c.pathPrefix ++ k := by
    intro hr
    apply List.IsSuffix.trans _ (List.suffix_append c.pathPrefix k)
    unfold prepareKeyM at hk
    split at hk
    · cases hk
    split at hk
    · cases hk
    split at hk
    · cases hk
    simp only at hk
    by_cases hc : opts.Recursive' = true ∧ ¬ go!"/" <:+ key
    · rw [ite_eq_left hc] at hk
      split at hk
      · obtain rfl := Option.some.inj hk
        exact List.suffix_append _ _
      · cases hk
    · rw [ite_eq_right hc] at hk
      split at hk
      · obtain rfl := Option.some.inj hk
        simp only [hr, true_and] at hc
        exact Classical.not_not.1 hc
      · cases hk
  wp_apply (wp_wWatch Obj wp sp c W γk ci' cd (c.pathPrefix ++ k) _ opts sie sel emp Q HQok Hhist
    Hnr hpfx hne hkl hsuf hn hpn hrt) $$ [$Hlt] as %wi %err ⟨Hlt, Hout⟩
  · iframe #
    ipureintro; exact Htb
  iapply HΦ
  iframe Hlt
  unfold kScopeOf
  iexact Hout

end proof

end k8s
end EtcdGrove
end Perennial
