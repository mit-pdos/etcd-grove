/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__Write.lean` (U2, `notes/bbolt-proof-plan.md`): `wp_proof'`, of `spec'`, the spec over the call a caller reaches (`ifaceCall`, `Lemmas/IfaceCall.lean`: the frozen spec's expression is unreachable); `wp_proof` stays `sorry` until the frozen spec is restated.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Write
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.IfaceCall
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__Write

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

/-- The spec, over the call a caller's code reaches (`ifaceCall`, `Lemmas/IfaceCall.lean`); the
rest is the frozen spec's. -/
abbrev Interface.Write.spec' : Prop :=
  ∀ (fli : GoInterface) (fl : FLPg) (p : Loc) (hdr : Page) (R : Nat),
  8 * (fl.allIds.length + 1) ≤ R → 0 < p.addr → p.addr + 16 + R ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flPgOwn fli fl ∗
      p ↦ hdr ∗ bytesPointsto (p +ₗ 16) (DFrac.own 1) (List.replicate R (W8 0)) }}
    (App (ifaceCall fli go!"Write") (Val #p))
  {{ RET #(); flPgOwn fli fl ∗
      let n := fl.allIds.length
      let body := (if n < 0xFFFF then [] else encode (W64 (n : Int))) ++
        (sortPgids fl.allIds).flatMap encode
      iprop(p ↦ (⟨hdr.id', W16 (freelistPageFlag : Int),
                     W16 ((if n < 0xFFFF then n else 0xFFFF : Nat) : Int), hdr.overflow'⟩ : Page) ∗
      bytesPointsto (p +ₗ 16) (DFrac.own 1) (body ++ List.replicate (R - body.length) (W8 0))) }}

theorem Interface.Write.wp_proof'
    (hFC : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.FreeCountSpec)
    (hFP : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.FreePageIdsSpec)
    (hMerge : _root_.Perennial.EtcdGrove.bbolt.Mergepgids.spec (GF := GF) (hG := hG))
    (hSF : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.SetFlags.spec (GF := GF) (hG := hG))
    (hSC : _root_.Perennial.EtcdGrove.bbolt.internal.common.Page.SetCount.spec (GF := GF) (hG := hG))
    (hUA : _root_.Perennial.EtcdGrove.bbolt.internal.common.UnsafeAdd.spec (GF := GF) (hG := hG)) :
    Interface.Write.spec' (GF := GF) (hG := hG) := by
  intro fli fl p hdr R HR Hp Hpb
  wp_start_folded as ⟨Hfl, Hh, Hb⟩
  icases flPgOwn_open _ _ $$ Hfl with ⟨%I, %a, %s, %HIf, #Hhdl, Hown, Hsh⟩
  obtain ⟨HI, Hfli⟩ := HIf
  subst Hfli
  have hFC' := hFC I a HI
  have hFP' := hFP I a HI
  rcases HI with rfl | rfl <;> (
    isimp only [arrayImpl, hashImpl] at Hhdl
    iface_dispatch
    wp_apply (shared.Write.wp_proof _ hFC' hFP' hMerge hSF hSC hUA s fl p hdr R HR Hp Hpb)
      $$ [Hsh Hown Hh Hb] as ⟨Hsh, Hown, Hh, Hb⟩
    · iframe
    iapply HΦ
    isplitl [Hown Hsh]
    · iapply flPgOwn_close _ a s _ fl (by first | exact Or.inl rfl | exact Or.inr rfl) rfl
      isplitl []
      · isimp only [arrayImpl, hashImpl]; iexact Hhdl
      isplitl [Hown]
      · isimp only [arrayImpl, hashImpl]; iexact Hown
      iexact Hsh
    dsimp only
    isimp only [flBody] at Hb
    rw [show (W16 ((freelistPageFlag : Nat) : Int) : w16) = W16 16 from rfl]
    iframe)

theorem Interface.Write.wp_proof : Interface.Write.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
