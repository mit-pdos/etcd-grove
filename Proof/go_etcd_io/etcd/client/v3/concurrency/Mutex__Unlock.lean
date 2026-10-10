/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Mutex__Unlock.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Mutex__Unlock
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutexLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Mutex.Unlock.wp_proof (hCl : Session.Client.spec (GF := GF) (hG := hG)) :
    Mutex.Unlock.spec (GF := GF) (hG := hG) := by
  intro m s γ client id pfx st ctx cs lo
  wp_start as ⟨#Hm, Hst, #Hctx, #Hlo⟩
  ihave #Hm' := Hm
  iunfold isMutex at Hm'
  icases Hm' with ⟨#Hms, #Hmpfx, %Hpfx, #Hsess, #Hcl⟩
  ihave Hci : (concurrencyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨-, -, ⟨%eL, #HeL⟩⟩
  unfold mutexState
  icases Hst with ⟨Hk, Hrv, Hh⟩
  wp_auto
  wp_if_destruct
  · -- myKey == ""
    iapply HΦ
    iright; ileft
    isplitr
    · unfold isPkgErr; iframe HeL; ipureintro; simp
    iframe
    ipureintro
    left; simpa using Hif
  wp_if_destruct
  · -- myRev <= 0
    iapply HΦ
    iright; ileft
    isplitr
    · unfold isPkgErr; iframe HeL; ipureintro; simp
    iframe
    ipureintro
    right; left; simpa using Hif
  wp_if_destruct
  · -- myKey == "\x00"
    iapply HΦ
    iright; ileft
    isplitr
    · unfold isPkgErr; iframe HeL; ipureintro; simp
    iframe
    ipureintro
    right; right; simpa using Hif
  rename_i Hk0 Hr0
  have Hnk : ¬ st.noKey := by
    unfold MutexSt.noKey
    have : sint.Z (W64 0) = 0 := by decide
    rw [this] at Hr0
    rintro (h | h | h)
    · exact Hk0 h
    · exact Hr0 h
    · exact Hif h
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply strings.wp_HasPrefix st.key pfx $$ [$Hstr]
  wp_if_destruct
  · wp_apply hCl s γ client id $$ [$Hpkg $Hsess]
    iunfold isEtcdMutexClient at Hcl
    icases Hcl with ⟨%kv, %wt, %cctx, %ccs, #HKV, -, -, -, -, -, #HDel, -⟩
    wp_auto
    ihave #Hnil := optsAt_nil (GF := GF)
    iunfold isEtcdDeleteKV at HDel
    wp_apply HDel $$ %ctx %cs %st.key %slice.nil %([] : List (OpFull → OpFull)) %lo [$Hctx $Hnil $Hlo] as %dresp %derr #Hd
    · ipureintro
      refine ⟨deleteOp_not_panics st.key, ?_⟩
      rw [(deleteOp_fields st.key).1, (deleteOp_fields st.key).2]
      exact keyRangeUnder_key pfx st.key Hif
    iunfold deleteResult at Hd
    icases Hd with (%Hne | ⟨%Heq, %r', %s', #Hr', %Hd, #Hts⟩)
    · obtain ⟨e, rfl⟩ : ∃ e, derr = GoInterface.ok e := by
        cases derr with
        | nil => exact absurd rfl Hne
        | ok e => exact ⟨e, rfl⟩
      wp_auto
      iapply HΦ
      iright; iright
      isplitr
      · ipureintro; exact Hne
      iframe
    subst Heq
    ihave #Habs := deleteTxn_absent pfx st.key r' s' $$ Hts
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists r'
    unfold MutexSt.released
    iframe
    iframe Hr' Habs
    ipureintro
    exact ⟨Hnk, Hif, Hd.1⟩
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply fmt.wp_Errorf $$ [$Hsl] as %e -
  iapply HΦ
  iright; iright
  iframe
  ipureintro; simp

end proof

end concurrency
end EtcdGrove
end Perennial
