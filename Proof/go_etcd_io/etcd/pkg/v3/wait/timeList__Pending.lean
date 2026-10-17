/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/timeList__Pending.lean`. Lean-first (no Rocq
counterpart; pr-verify/etcd-22495, 2026-10-17).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.timeList__Pending

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

theorem wait.timeList.Pending.wp_proof : wait.timeList.Pending.spec (GF := GF) (hG := hG) := by
  intro tl P
  wp_start as #Htl
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTimeList at Htl
  icases Htl with ⟨%mref, #Hm, #Hmu, #Hmono, #Hcl⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold timeListR at HR
  icases HR with ⟨%last, %M, %hs, %xs, Hlast, HM, #Hlastp, Hchs, Hh, Hs, Hcap, %Hok⟩
  (try wp_auto)
  wp_apply wp_map_len_lt $$ [$HM] as ⟨HM, %Hsz⟩
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlast HM Hchs Hh Hs Hcap]
  · inext; iunfold timeListR; iexists last, M, hs, xs; iframe; iframe #; ipureintro; exact Hok
  (try wp_auto)
  iapply HΦ
  ipureintro
  word

end proof

end EtcdGrove
end Perennial
