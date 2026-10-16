/-
Proof of `Spec/go_etcd_io/etcd/client/v3/newBlockLogger.lean` (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.newBlockLogger
public import Perennial.Proof.time
public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem newBlockLogger.wp_proof :
    newBlockLogger.spec (GF := GF) (hG := hG) := by
  intro α A iv th nowf lf
  wp_start as ⟨#Hnow, #Hlf⟩
  wp_auto
  iapply wp_fupd
  wp_if_destruct
  · wp_apply time.wp_Now as %t0 -
    ihave #Hnf : (□ ∀ Φ : val → IProp GF, ▷ (∀ t : _root_.Perennial.time.Time, Φ #t) -∗
        WP (App (Val #(functions _root_.Perennial.time.Now [])) (Val #())) {{ Φ }}) $$ []
    · imodintro; iintro %Φ' HΦ'
      wp_apply time.wp_Now as %t1 -
      iapply HΦ'
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
    iStructNamed «$r0»
    ipersist interval; ipersist threshold; ipersist now; ipersist logFunc
    imod sync.init_Mutex iprop(∃ (t : _root_.Perennial.time.Time) (n : w64)
        (d : _root_.Perennial.time.Duration),
        structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"lastLogTime" «$r0_ptr» ↦ t ∗
        structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"eventCount" «$r0_ptr» ↦ n ∗
        structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"timeWaiting" «$r0_ptr» ↦ d) ⊤
        _ $$ mu [lastLogTime eventCount timeWaiting] with #Hlock
    · inext; iexists _, _, _; iframe
    imodintro
    iapply HΦ
    unfold isBlockLogger
    iexists _, lf, iv, th
    iframe #
    ipureintro; exact Hnn
  · icases Hnow with (%Hn | #Hnf)
    · exact absurd Hn (by assumption)
    wp_apply Hnf as %t0
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
    iStructNamed «$r0»
    ipersist interval; ipersist threshold; ipersist now; ipersist logFunc
    imod sync.init_Mutex iprop(∃ (t : _root_.Perennial.time.Time) (n : w64)
        (d : _root_.Perennial.time.Duration),
        structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"lastLogTime" «$r0_ptr» ↦ t ∗
        structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"eventCount" «$r0_ptr» ↦ n ∗
        structFieldRef go_etcd_io.etcd.client.v3.blockLogger go!"timeWaiting" «$r0_ptr» ↦ d) ⊤
        _ $$ mu [lastLogTime eventCount timeWaiting] with #Hlock
    · inext; iexists _, _, _; iframe
    imodintro
    iapply HΦ
    unfold isBlockLogger
    iexists _, lf, iv, th
    iframe #
    ipureintro; exact Hnn

end proof

end EtcdGrove
end Perennial
