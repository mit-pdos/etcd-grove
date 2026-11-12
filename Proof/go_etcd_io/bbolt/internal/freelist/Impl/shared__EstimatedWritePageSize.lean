/-
`shared.EstimatedWritePageSize()` (U2 internal).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__Count

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.EstimatedWritePageSize()`: a header, and 8 bytes per free or pending id, plus one for
the count from `0xFFFF` ids on. -/
abbrev shared.EstimatedWritePageSize.spec (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (fl : FLPg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
      ownSh s I.iface fl ∗ I.own fl.free }}
    (App (Val #(methods (go.GoType.PointerType shared.ty) go!"EstimatedWritePageSize" #s))
      (Val #()))
  {{ RET #(W64 ((16 + 8 * (fl.allIds.length +
        (if 0xFFFF ≤ fl.allIds.length then 1 else 0)) : Nat) : Int));
      ownSh s I.iface fl ∗ I.own fl.free }}

theorem shared.EstimatedWritePageSize.wp_proof (I : FLImpl (GF := GF)) (hFC : I.FreeCountSpec) :
    shared.EstimatedWritePageSize.spec I := by
  intro s fl
  wp_start as ⟨Hsh, Hown⟩
  iunfold ownSh at Hsh
  icases Hsh with ⟨%c, Hsh, %Hok⟩
  have Hlen : fl.allIds.length < 2 ^ 63 := Hok.2.2.2.2.1
  wp_auto
  wp_apply (shared.Count.wp_proof I hFC s fl c) $$ [Hsh Hown] as ⟨Hsh, Hown⟩
  · iframe
  wp_if_destruct
  · rw [if_pos (by word)]
    rw [show W64 16 + W64 8 * (W64 (fl.allIds.length : Int) + W64 1) =
      W64 ((16 + 8 * (fl.allIds.length + 1) : Nat) : Int) by word]
    iapply HΦ; iframe
    iunfold ownSh; iexists c; iframe; ipureintro; exact Hok
  · rw [if_neg (by word)]
    rw [show W64 16 + W64 8 * W64 (fl.allIds.length : Int) =
      W64 ((16 + 8 * (fl.allIds.length + 0) : Nat) : Int) by word]
    iapply HΦ; iframe
    iunfold ownSh; iexists c; iframe; ipureintro; exact Hok
end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
