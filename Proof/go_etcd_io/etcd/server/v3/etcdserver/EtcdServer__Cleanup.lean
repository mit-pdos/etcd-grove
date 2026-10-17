/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Cleanup.lean` (etcd PR #22190's
verification; an axiom, names-only, until then). Lean-first; see `InvBackendLife.lean`.

The closer's flag excludes the shut case of `bemu`'s resource, so the write lock gives all of the
backend's open token, which `Close` takes; the resource goes back shut, with `stopping`'s done
view.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Cleanup

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option hygiene false in
/-- `if x != nil { x.Stop() }` (or `Close`) of a contract `H` (`stopOk`/`closeOk`), on every goal:
nil, skipped; else the method's contract. -/
local macro "cl_call " H:ident : tactic => `(tactic| (
  (try iunfold stopOk at $H:ident)
  (try iunfold closeOk at $H:ident)
  icases $H:ident with (%Hn | ⟨%vi, %Hvi, #Hm⟩)
  all_goals (first
    | (rw [Hn]; (try wp_auto))
    | (rw [Hvi]; (try wp_auto); (first | wp_apply Hm as %er - | wp_apply Hm);
        (try wp_auto)))))

set_option hygiene false in
/-- `if s.be != nil { s.bemu.Lock(); s.be.Close(); s.bemu.Unlock() }` with `s.be` the interface
`GoInterface.ok bi`: the closer's flag excludes the shut case, `Close` takes the whole open token,
the resource goes back shut. -/
local macro "cl_be" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply (lc := 1) sync.RWMutex.wp_Lock $$ [Hrw] as ⟨Hwl, HP⟩
  · iframe Hrw
  imod lc_fupd_elim_later $$ Hlc1 HP with HP
  iunfold bemuP at HP
  icases HP with ⟨%b', Hb', #Hok, Hst⟩
  icombine Hbh Hb' gives %Hbeq
  subst Hbeq
  ihave ⟨HO, Hcl'⟩ : iprop(L.O 1 ∗ beCloser L) $$ [Hst Hcl]
  · icases Hst with (HO | #Hshut)
    · iframe HO Hcl
    · iexfalso
      iapply beCloser_not_shut s L $$ [Hcl] []
      · iexact Hcl
      · iexact Hshut
  ihave #Hok' := Hok
  iunfold beLifeOk at Hok'
  icases Hok' with ⟨-, %bi', %Hbi', -, #HClose⟩
  simp only [GoInterface.ok.injEq] at Hbi'
  subst Hbi'
  (try wp_auto)
  wp_apply HClose $$ [HO] as %err -
  · iexact HO
  imod beCloser_shut s L ch γ $$ Hcl' Hch Hd with #Hshut
  wp_apply sync.RWMutex.wp_Unlock $$ [Hwl Hb' Hok Hshut] as -
  · iframe Hwl; inext; iunfold bemuP; iexists (GoInterface.ok bi); iframe Hb' Hok
    iright; iexact Hshut
  (try wp_auto)))

theorem EtcdServer.Cleanup.wp_proof : EtcdServer.Cleanup.spec (GF := GF) (hG := hG) := by
  intro s ch γ
  wp_start as ⟨Hres, #Hch, #Hd⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold srvCleanupRes at Hres
  icases Hres with ⟨%L, %b, Hrw, Hcl, Hbh, ⟨%lv, #Hlf, #Hlok⟩, ⟨%kv, #Hkf, #Hkok⟩,
    ⟨%av, #Haf, #Haok⟩, ⟨%cv, #Hcf, #Hcok⟩⟩
  cases b with
  | nil =>
    -- `s.be` nil: no close
    (try wp_auto)
    cl_call Hlok
    all_goals cl_call Hkok
    all_goals cl_call Haok
    all_goals (try wp_auto)
    all_goals cl_call Hcok
    all_goals (iapply HΦ; itrivial)
  | ok bi =>
    (try wp_auto)
    cl_call Hlok
    all_goals cl_call Hkok
    all_goals cl_call Haok
    all_goals cl_be
    all_goals cl_call Hcok
    all_goals (iapply HΦ; itrivial)

end proof

end EtcdGrove
end Perennial
