/-
`newTokenProviderSimple`'s proof (the auth plan's E2g, 2026-10-25; until then
`tokenSimple_new`, S5e): the logger (`zap.NewNop()` for a nil one), the empty token map, the
provider's struct; for a positive TTL, fresh names (the rights' authority `γf`, the issued tokens'
`γt`, the keepers' ghost set `γk`) and the mutex with the lock invariant `simpleLk` (no token, no
keeper). The index waiter's field is made read-only either way.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.newTokenProviderSimple.wp_proof (h_NewNop : zap.NewNop.spec (GF := GF) (hG := hG)) :
    auth.newTokenProviderSimple.spec (GF := GF) (hG := hG) := by
  intro lg iw ttl
  wp_start
  iapply wp_fupd
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  wp_if_destruct
  · wp_apply h_NewNop as %lg' %Hlg'
    (try wp_auto)
    wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mp Hm
    (try wp_auto)
    irename «$r0» => Hp
    generalize «$r0_ptr» = p at *
    iStructNamed Hp
    ipersist lg
    ipersist indexWaiter
    by_cases hpos : 0 < sint.Z ttl
    · imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Unit)) with ⟨%γf, Hf⟩
      imod (tokAlloc (GF := GF) γf) with ⟨%γt, Htok⟩
      imod (ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Unit)) with ⟨%γk, Hka⟩
      ihave ⟨Hk1, Hk2⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ simpleTokenKeeper
      imod sync.init_Mutex (simpleLk p γt γf γk) ⊤ (tsF go!"simpleTokensMu" p)
        $$ [simpleTokensMu] [simpleTokens Hm Htok Hk1 Hka simpleTokenTTL] with #Hmu
      · iexact simpleTokensMu
      · inext
        iunfold simpleLk
        iexists mp, ∅, null, ∅, ttl, ∅
        iframe
        isplitl []
        · iapply BigSepM.bigSepM_empty.2; itrivial
        isplitr
        · ipureintro; left; rfl
        isplitl []
        · iapply BigSepM.bigSepM_empty.2; itrivial
        ipureintro; exact hpos
      (try wp_auto)
      imodintro
      iapply HΦ
      iframe #
      iright
      iexists γt, γf
      iframe Hf
      isplitr
      · iunfold simpleOk
        iexists lg', γk
        iframe #
        ipureintro; exact Hlg'
      iunfold simpleAdmin
      iexists null
      iframe Hk2
      ileft; ipureintro; rfl
    · (try wp_auto)
      imodintro
      iapply HΦ
      iframe #
      ileft; ipureintro; omega
  · wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %mp Hm
    (try wp_auto)
    irename «$r0» => Hp
    generalize «$r0_ptr» = p at *
    iStructNamed Hp
    ipersist lg
    ipersist indexWaiter
    by_cases hpos : 0 < sint.Z ttl
    · imod (ghost_map_alloc_empty (GF := GF) (K := GoString) (V := Unit)) with ⟨%γf, Hf⟩
      imod (tokAlloc (GF := GF) γf) with ⟨%γt, Htok⟩
      imod (ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Unit)) with ⟨%γk, Hka⟩
      ihave ⟨Hk1, Hk2⟩ := (typedPointsto_half_split _ _ (1 : Qp)).1 $$ simpleTokenKeeper
      imod sync.init_Mutex (simpleLk p γt γf γk) ⊤ (tsF go!"simpleTokensMu" p)
        $$ [simpleTokensMu] [simpleTokens Hm Htok Hk1 Hka simpleTokenTTL] with #Hmu
      · iexact simpleTokensMu
      · inext
        iunfold simpleLk
        iexists mp, ∅, null, ∅, ttl, ∅
        iframe
        isplitl []
        · iapply BigSepM.bigSepM_empty.2; itrivial
        isplitr
        · ipureintro; left; rfl
        isplitl []
        · iapply BigSepM.bigSepM_empty.2; itrivial
        ipureintro; exact hpos
      (try wp_auto)
      imodintro
      iapply HΦ
      iframe #
      iright
      iexists γt, γf
      iframe Hf
      isplitr
      · iunfold simpleOk
        iexists lg, γk
        iframe #
        ipureintro; exact Hif
      iunfold simpleAdmin
      iexists null
      iframe Hk2
      ileft; ipureintro; rfl
    · (try wp_auto)
      imodintro
      iapply HΦ
      iframe #
      ileft; ipureintro; omega

end proof

end EtcdGrove
end Perennial
