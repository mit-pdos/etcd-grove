/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/LeaseExpiredNotifier__Len.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseExpiredNotifier__Len

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.LeaseExpiredNotifier.Len.wp_proof :
    lease.LeaseExpiredNotifier.Len.spec (GF := GF) (hG := hG) := by
  intro np q M
  wp_start as Hn
  iunfold notifierAtM at Hn
  icases Hn with ⟨%mp, %s, %xs, Hm, HM, Hq, Hqa, %Hinv⟩
  wp_auto
  wp_apply (wp_map_len_lt (t := go.GoType.MapType LeaseID.ty (go.GoType.PointerType LeaseWithTime.ty))
    mp M (DFrac.own q)) $$ [$HM] as ⟨HM, %Hlt⟩
  (try wp_auto)
  iapply HΦ
  isplitl
  · iunfold notifierAtM; iexists mp, s, xs; iframe; ipureintro; exact Hinv
  ipureintro; exact Hlt

end proof

end EtcdGrove
end Perennial
