/-
The proof of `Spec/go_etcd_io/bbolt/TxStats__IncSplit.lean` (U5, `notes/bbolt-proof-plan.md`): the atomic operation on the statistics field, inside `txsInv` (`stats_open`).
-/
module

public import Spec.go_etcd_io.bbolt.TxStats__IncSplit
public import Proof.go_etcd_io.bbolt.Txn.Stats

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem TxStats.IncSplit.wp_proof : TxStats.IncSplit.spec (GF := GF) (hG := hG) := by
  intro K tx r m q d
  wp_start as ⟨#Hc, #Hreg, Ht⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt $$ []
  · unfold BC.core isBoltCoreP
    icases Hc with ⟨-, -, -, $, -⟩
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_AddInt64 $$ [] [Ht HΦ «$res0»]
  · iexact Hatomic
  imod stats_open K tx r m q ⊤ CoPset.subseteq_top $$ [Ht] with ⟨%s, Hs, Hcl⟩
  · iframe Hc Hreg Ht
  icases (TxStats.TxStats_access_store_Split _ s (s.Split' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s.Split'
  iframe Hf
  iintro Hf
  imod Hmask with -
  imod Hcl $$ [Hclose Hf] with Ht
  · iapply Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ht

end proof

end bbolt
end EtcdGrove
end Perennial
