/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/lessor__Lookup.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Lookup
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.lessor.Lookup.wp_proof : lease.lessor.Lookup.spec (GF := GF) (hG := hG) := by
  intro lp γl id q L
  wp_start as ⟨#Hinv, Hrd, Hown⟩
  iunfold lessorInv at Hinv
  icases Hinv with ⟨%Hlp, #Hpin, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold lessorRd at Hrd
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HR⟩
  iunfold lessorMu at HR
  icases HR with ⟨%lm, %im, %M, %I, %rd0, %L', Hlm, HM, Him, HI, Hrdf, Ha, Hg, %HL, #Hls, Hx⟩
  ihave %Hag := leaseFrag_agree γl _ _ _ _ $$ [$Hown $Hg]
  subst Hag
  wp_auto
  wp_apply (wp_map_lookup1 LeaseID.ty (go.GoType.PointerType Lease.ty) lm M id) $$ HM as HM
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hlm HM Him HI Hrdf Ha Hg Hx] as Hrd
  · inext
    iunfold lessorMu
    iexists lm, im, M, I, rd0, L
    iframe
    iframe Hls
    ipureintro; exact HL
  iapply HΦ
  iunfold lessorRd
  iframe Hrd Hown
  have hL := HL id
  cases hM : M.lookup id with
  | none =>
    simp only [Option.getD_none]
    isplitr
    · ipureintro
      simp only [hM, Option.isSome_none, Bool.false_eq_true, iff_false] at hL
      exact ⟨fun _ => hL, fun _ => rfl⟩
    ileft; ipureintro; rfl
  | some l =>
    simp only [Option.getD_some]
    ihave #Hl := BigSepM.bigSepM_lookup hM $$ Hls
    iunfold isLeaseObj at Hl
    icases Hl with ⟨%Hnn, #Hlmu⟩
    isplitr
    · ipureintro
      simp only [hM, Option.isSome_some, iff_true] at hL
      exact ⟨fun h => absurd h Hnn, fun h => absurd hL h⟩
    iright
    iunfold isLeaseObj
    iframe Hlmu
    ipureintro; exact Hnn

end proof

end EtcdGrove
end Perennial
