/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/newTokenProviderSimple.lean` (pr-verify etcd#22560, 2026-10-16).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.newTokenProviderSimple
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.newTokenProviderSimple.wp_proof
    (h_NewNop : zap.NewNop.spec (GF := GF) (hG := hG)) :
    auth.newTokenProviderSimple.spec (GF := GF) (hG := hG) := fun lg iw ttl => by
  wp_start
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_auto
  wp_join iprop(∃ lg' : Loc, lg_ptr ↦ lg' ∗ ⌜lg' ≠ null⌝) with [lg] as ⟨%lg', lg, %Hlg⟩
  · wp_apply h_NewNop as %l %Hl
    wp_join_done
    iexists l
    iframe
    ipureintro; exact Hl
  · iexists lg
    iframe
    ipureintro; assumption
  wp_apply wp_map_make1 (K := GoString) (V := GoString) as %sp Hspm
  wp_apply wp_map_make1 (K := GoString) (V := GoString) as %ep Hepm
  wp_alloc t as Ht
  ihave %Htnn := typedPointsto_not_null _ _ _ $$ Ht
  iStructNamed Ht
  imod ghostVar_alloc (GF := GF) (∅ : GMap GoString GoString) with ⟨%γ, Hv⟩
  icases ghostVar_split γ (∅ : GMap GoString GoString) (1 : Qp).half (1 : Qp).half $$ [Hv] with ⟨Hv1, Hv2⟩
  · rw [Qp.half_add_half]; iexact Hv
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Unit) with ⟨%γk, HK⟩
  icases (ts_ptsto_halves _ _).1 $$ simpleTokenKeeper with ⟨Hkp1, Hkp2⟩
  ipersist lg
  imod sync.init_Mutex (stLockP t γ γk) ⊤ (tMu t) $$ simpleTokensMu
    [Hkp1 Hv1 simpleTokens Hspm expiredTokens Hepm simpleTokenTTL HK] with #Hmu
  · inext
    iunfold stLockP
    iexists null, ∅, ∅, ttl
    iframe
    isplitl [simpleTokens Hspm expiredTokens Hepm]
    · iunfold stTables
      iexists sp, ep, ∅, ∅
      iframe
      ipureintro; exact ⟨subseteq_empty _, subseteq_empty _⟩
    isplitr
    · iapply (BigSepM.bigSepM_empty (Φ := fun k (_ : Unit) => iprop(k ↪[γk]□ () : IProp GF))).2
      iempintro
    isplitr
    · iapply (BigSepM.bigSepM_empty (Φ := fun k (_ : Unit) => keeperMap (GF := GF) k)).2
      iempintro
    · ileft; ipureintro; rfl
  wp_auto
  iapply HΦ
  iexists γ, γk
  isplitr
  · iunfold isTS
    iframe #
    ipureintro; exact ⟨Htnn, Hlg⟩
  · iunfold tsAdmin
    iframe

end proof

end EtcdGrove
end Perennial
