/- Lean-first (no Rocq counterpart). The proof of `runner.openBackend`: Draft, to come.

The outline: `DefaultBackendConfig` (`mvccrand.wp_DefaultBackendConfig`: no hooks, the default
limit), the fields set, `backend.New` (its `hooksOk` at no hook; the panic arm refuted by
`dbOpenOk`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__openBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.New

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

omit mvcc_sem srv_sem in
open go_etcd_io.etcd.server.v3.storage.backend in
/-- `mvccrand.wp_DefaultBackendConfig`, restated here: mvccrand's carries mvccrand's package
assumptions (a section variable of its file), which nothing here has. -/
private theorem wp_DefaultBackendConfig' (lg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend }}
      (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.DefaultBackendConfig)) (Val #lg))
    {{ (c : BackendConfig), RET #c; ⌜c.BatchLimit' = W64 10000 ∧ c.Hooks' = GoInterface.nil⌝ }} := by
  wp_start as #Hpkg
  ihave Hbi : (backendInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hbi with ⟨-, -, -, -, -, #Hbi, #Hbl, #Hms⟩
  wp_auto
  iapply HΦ
  ipureintro
  exact ⟨rfl, rfl⟩

theorem runner.openBackend.wp_proof
    (wp_bNew : backend.New.spec (GF := GF) (hG := hG)) :
    runner.openBackend.spec (GF := GF) (hG := hG) := by
  intro _ x ks cfg wr h γh path D W Pk K hdbo hlim
  wp_start as ⟨#Hctx, Hfile, #Hvoff, Htok, Hup⟩
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hrn, -, -, -, #Hbpkg, -, -, -, -, ⟨%lg, #Hlg, -⟩, -⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨-, -, -, -, -, -, #Hcfg, -⟩
  icases typedPointsto_split _ _ _ $$ Hcfg with #Hcfg
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hcfg
  wp_auto
  wp_apply wp_DefaultBackendConfig' as %bc %Hbc
  obtain ⟨hdl, hhooks⟩ := Hbc
  (try wp_auto)
  -- the batch limit set: `limOf cfg` (the interval, any)
  have hW0 : sint.Z (W64 0) = 0 := rfl
  by_cases hb : 0 < sint.Z cfg.BatchLimit' <;>
    simp only [hW0, hb, decide_true, decide_false] <;> wp_auto <;>
    (by_cases hi : 0 < sint.Z cfg.BatchInterval' <;>
      simp only [hW0, hi, decide_true, decide_false] <;> wp_auto)
  all_goals
    have hl0 : 0 < sint.Z (limOf cfg) := by
      unfold limOf; split
      · assumption
      · word
    wp_apply (wp_bNew _ (mvccrand.rcP (limOf cfg)) D W Pk K) $$ [Hfile Htok Hup] as %r Hr
    · iframe Hfile Htok Hvoff Hup
      isplitr
      · ipureintro
        refine ⟨mvccrand.rcP_wf _ hl0 hlim, ?_⟩
        show limOf cfg = _
        unfold limOf
        simp only [hb, ↓reduceIte, hdl]
      · iunfold backend.hooksOk
        iintro !> %γ %b %t _ _
        iunfold backend.hooksSpec
        ileft; ipureintro; exact hhooks
    icases Hr with (⟨%b, %γB, %Hr, Hnew, -, Hbf, Htok⟩ | %Hpan)
    rotate_left
    · exact absurd hdbo Hpan.1
    subst Hr
    (try wp_auto)
    iapply HΦ
    iframe Htok
    iexists b, γB
    iframe Hnew Hbf
    ipureintro; rfl

end proof

end mvccfull
end EtcdGrove
end Perennial
