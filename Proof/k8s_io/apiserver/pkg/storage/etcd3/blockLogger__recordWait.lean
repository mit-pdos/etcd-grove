/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/blockLogger__recordWait.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.blockLogger__recordWait
public import Spec.k8s_io.klog.v2.V
public import Spec.k8s_io.klog.v2.Verbose__InfoS
public import Perennial.Proof.time.PtrMethods
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem blockLogger.recordWait.wp_proof
    (wp_V : klog.V.spec (GF := GF) (hG := hG))
    (wp_InfoS : klog.Verbose.InfoS.spec (GF := GF) (hG := hG))
    (wp_Sub : time.Time.Sub.spec (GF := GF) (hG := hG)) :
    blockLogger.recordWait.spec (GF := GF) (hG := hG) := by
  intro l d
  unfold blockLoggerOk
  wp_start as ⟨%iv, %th, %msg, %ot, %gr, %ck, #Hiv, %hmsg, #Hth, #Hmsg, #Hot, #Hgr, #Hck, #Hnow, #Hmu⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply (sync.Mutex.wp_Lock _ (blockLoggerInv l)) $$ [] as ⟨Hlocked, HR⟩
  · iframe #
  iunfold blockLoggerInv at HR
  icases HR with ⟨%lt, %ec, %tw, Hlt, Hec, Htw⟩
  (try wp_auto)
  iunfold clockNowOk at Hnow
  wp_apply Hnow as %now
  (try wp_auto)
  wp_apply (time.Time.wp_ptr_Sub_of wp_Sub) $$ [$now] as %w now
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    wp_apply (sync.Mutex.wp_Unlock _ (blockLoggerInv l)) $$ [Hlocked Hlt Hec Htw]
    · iframe #
      iframe Hlocked
      inext
      iunfold blockLoggerInv
      iexists _, _, _
      iframe
    (try wp_auto)
    iapply HΦ; itrivial
  · (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      ihave #Pklog : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.klog.v2 $$ []
      · iPkgInit
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      (try wp_auto)
      wp_apply wp_V as %v %hv
      (try wp_auto)
      wp_apply wp_InfoS v msg _ _ _ hv hmsg ?_ $$ [$Hsl] as -
      · intro x hx
        rw [show sint.nat (W64 (0 + 1)) = 1 by rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 by rfl, show sint.nat (W64 (0 + 1 + 1 + 1)) = 3 by rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1)) = 4 by rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1)) = 5 by rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1)) = 6 by rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = 7 by rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = 8 by rfl, show sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = 9 by rfl] at hx
        simp only [List.set_cons_succ, List.set_cons_zero, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact ⟨_, rfl, by simp⟩
      (try wp_auto)
      wp_apply (sync.Mutex.wp_Unlock _ (blockLoggerInv l)) $$ [Hlocked Hlt Hec Htw]
      · iframe #
        iframe Hlocked
        inext
        iunfold blockLoggerInv
        iexists _, _, _
        iframe
      (try wp_auto)
      iapply HΦ; itrivial
    · (try wp_auto)
      wp_apply (sync.Mutex.wp_Unlock _ (blockLoggerInv l)) $$ [Hlocked Hlt Hec Htw]
      · iframe #
        iframe Hlocked
        inext
        iunfold blockLoggerInv
        iexists _, _, _
        iframe
      (try wp_auto)
      iapply HΦ; itrivial

end proof

end k8s
end EtcdGrove
end Perennial
