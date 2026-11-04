/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__RemoveReadonlyTXID.lean` (U2, `notes/bbolt-proof-plan.md`): `wp_proof'`, of `spec'`, the spec over the call a caller reaches (`ifaceCall`, `Lemmas/IfaceCall.lean`: the frozen spec's expression is unreachable); `wp_proof` stays `sorry` until the frozen spec is restated.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__RemoveReadonlyTXID
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.IfaceCall
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__readonly

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

abbrev Interface.RemoveReadonlyTXID.spec' : Prop :=
  ∀ (fli : GoInterface) (ro : List w64) (tid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flRoOwn fli ro }}
    (App (ifaceCall fli go!"RemoveReadonlyTXID") (Val #tid))
  {{ RET #(); ∃ ro', flRoOwn fli ro' ∗ ⌜ro'.Perm (ro.erase tid)⌝ }}

theorem Interface.RemoveReadonlyTXID.wp_proof' : Interface.RemoveReadonlyTXID.spec' (GF := GF) (hG := hG) := by
  intro fli ro tid
  wp_start_folded as Hro
  iunfold flRoOwn at Hro
  icases Hro with ⟨%a, %s, %sl, Himpl, Hf, Hsl, Hcap⟩
  iunfold flImplAt at Himpl
  icases Himpl with (⟨%Hfli, #Hhdl⟩ | ⟨%Hfli, #Hhdl⟩) <;> (
    subst Hfli
    first
      | rw [show interface.mkOk (go.GoType.PointerType array'.ty) #a = (arrayImpl (GF := GF) a).iface
          from rfl]
      | rw [show interface.mkOk (go.GoType.PointerType hashMap.ty) #a = (hashImpl (GF := GF) a).iface
          from rfl]
    iface_dispatch
    wp_apply (shared.RemoveReadonlyTXID.wp_proof s ro tid) $$ [Hf Hsl Hcap] as HRO
    · iunfold roOwn; iexists sl; iframe
    iapply HΦ
    icases HRO with ⟨%ro', HRO, %Hp⟩
    iunfold roOwn at HRO
    icases HRO with ⟨%sl', Hf, Hsl, Hcap⟩
    iexists ro'
    isplitl
    · iunfold flRoOwn
      iexists a, s, sl'
      iframe
      first | iapply flImplAt_array $$ Hhdl | iapply flImplAt_hash $$ Hhdl
    · ipureintro; exact Hp)

theorem Interface.RemoveReadonlyTXID.wp_proof : Interface.RemoveReadonlyTXID.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
