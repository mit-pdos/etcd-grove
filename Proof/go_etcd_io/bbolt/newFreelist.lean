/-
The proof of `Spec/go_etcd_io/bbolt/newFreelist.lean` (U2, `notes/bbolt-proof-plan.md`), over the two constructors' specs
(`Proof/go_etcd_io/bbolt/internal/freelist/Impl/New{Array,HashMap}Freelist.lean`).
-/
module

public import Spec.go_etcd_io.bbolt.newFreelist
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.NewArrayFreelist
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.NewHashMapFreelist

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

theorem newFreelist.wp_proof : newFreelist.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start
  wp_auto
  ihave #Hfpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist $$ []
  · iPkgInit
  wp_if_destruct
  · wp_apply (internal.freelist.NewHashMapFreelist.wp_proof) as %fli ⟨%Hnn, Hpg, Hro⟩
    iapply HΦ
    iframe
    ipureintro; exact Hnn
  · wp_apply (internal.freelist.NewArrayFreelist.wp_proof) as %fli ⟨%Hnn, Hpg, Hro⟩
    iapply HΦ
    iframe
    ipureintro; exact Hnn

end proof

end bbolt
end EtcdGrove
end Perennial
