/-
The proof of `Spec/go_etcd_io/bbolt/internal/freelist/Interface__ReleasePendingPages.lean` (U2, `notes/bbolt-proof-plan.md`),
over `ifaceCall` (`Inv/Freelist.lean`; dispatch: `Lemmas/IfaceCall.lean`).
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__ReleasePendingPages
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.IfaceCall
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.shared__ReleasePendingPages

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem Interface.ReleasePendingPages.wp_proof
    (hMS : ∀ (I : FLImpl (GF := GF)) a, I.IsImpl a → I.MergeSpansSpec) :
    Interface.ReleasePendingPages.spec (GF := GF) (hG := hG) := by
  intro fli fl ro
  rw [← FLPg.releasePendingGo_eq]
  wp_start_folded as ⟨Hfl, Hro⟩
  icases flPgOwn_open _ _ $$ Hfl with ⟨%I, %a, %s, %HIf, #Hhdl, Hown, Hsh⟩
  obtain ⟨HI, Hfli⟩ := HIf
  subst Hfli
  have hMS' := hMS I a HI
  have hI' := HI
  iunfold flRoOwn at Hro
  icases Hro with ⟨%a', %s', %sl, Himpl, Hf, Hsl, Hcap⟩
  iunfold flImplAt at Himpl
  rcases HI with rfl | rfl <;> (
    icases Himpl with (⟨%Hfli, #Hhdl'⟩ | ⟨%Hfli, #Hhdl'⟩) <;>
      (first
        | (exfalso; exact mkOk_array_ne_hash _ _ Hfli)
        | (exfalso; exact mkOk_array_ne_hash _ _ Hfli.symm)
        | skip)
    all_goals
      simp only [FLImpl.iface, arrayImpl, hashImpl, interface.mkOk, GoInterface.ok.injEq,
        GoInterfaceOk.mk.injEq, _root_.true_and] at Hfli
      have Ha : a = a' := go.intoVal_inj Hfli
      subst Ha
      isimp only [arrayImpl, hashImpl] at Hhdl
      icombine Hhdl Hhdl' gives %Hss
      subst Hss
      iface_dispatch
      wp_apply (shared.ReleasePendingPages.wp_proof _ hMS' s fl ro) $$ [Hsh Hown Hf Hsl Hcap]
        as ⟨Hsh, Hown, HRO⟩
      · iframe
        iunfold roOwn; iexists sl; iframe
      iapply HΦ
      isplitl [Hsh Hown]
      · iapply flPgOwn_close _ a s _ _ hI' rfl
        isplitl []
        · isimp only [arrayImpl, hashImpl]; iexact Hhdl
        isplitl [Hown]
        · isimp only [arrayImpl, hashImpl]; iexact Hown
        iexact Hsh
      iunfold roOwn at HRO
      icases HRO with ⟨%sl', Hf, Hsl, Hcap⟩
      iunfold flRoOwn
      iexists a, s, sl'
      iframe
      first | iapply flImplAt_array $$ Hhdl | iapply flImplAt_hash $$ Hhdl)

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
