/- Lean-first (no Rocq counterpart).

The proof of `service.Svc.Echo.spec`: under `s.mu`, the map of runs has no entry for `id` (its
entry would hold a second token of `id`, `idTok_excl`), so the run counts `1`; the entry `id ↦ 1`
goes back into the invariant with the request's token. Then the reply's fields, and the error
(`errors.New(a.Fail)`, `errMsg`) if `Fail` is not empty.
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service.Svc__Echo
public import Net.Proof.net.rpc.Errs
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : service.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

set_option goose.wp.extras true

theorem Svc.Echo.wp_proof : Svc.Echo.spec (GF := GF) (hG := hG) := by
  intro γid s a r id dsl fail v
  wp_start as ⟨#Hsvc, Ha, Hr, Htok⟩
  iunfold isSvc at Hsvc
  icases Hsvc with ⟨#Hpkg, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock (muAddr s) (svcInv γid s) $$ [$Hmu] as ⟨Hlk, Hinv⟩
  iunfold svcInv at Hinv
  icases Hinv with ⟨%mref, %m, Hruns, Hm, Hbig⟩
  cases hlk : m.lookup id with
  | some n =>
    icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m id = some n by
      rw [gmap_get?_eq]; exact hlk)).1 $$ Hbig with ⟨⟨-, Htok2⟩, -⟩
    icases idTok_excl γid id $$ Htok Htok2 with ⟨⟩
  | none =>
    have hv0 : (m !! id).getD (zero_val w64) = W64 0 := by
      rw [show m !! id = none from hlk]; rfl
    have h01 : (W64 0 + W64 1 : w64) = W64 1 := by decide
    wp_auto
    wp_apply +noauto (wp_map_lookup1 (K := w64) (V := w64) go.uint64 go.uint64 mref m id
      (DFrac.own 1)) $$ Hm as Hm
    rw [hv0]
    wp_auto
    (try rw [h01])
    wp_apply (wp_mapInsert (K := w64) (V := w64) go.uint64 mref m id _) $$ Hm as Hm
    wp_apply +noauto (wp_map_lookup1 (K := w64) (V := w64) go.uint64 go.uint64 mref
      _ id (DFrac.own 1)) $$ Hm as Hm
    rw [GMap.lookup_insert, Option.getD_some]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock (muAddr s) (svcInv γid s) $$ [$Hmu $Hlk Hruns Hm Hbig Htok]
    · unfold svcInv
      iexists mref, _
      iframe Hruns Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m id = none by
        rw [gmap_get?_eq]; exact hlk)).2
      iframe Hbig Htok
      (try (ipureintro; first | rfl | decide | exact h01))
    wp_if_destruct
    all_goals (try (wp_apply net.rpc.wp_errors_New' as %x #HN))
    all_goals (
      iapply HΦ
      iframe Ha
      isplitl [Hr]
      · iexact Hr)
    all_goals first
      | (ileft; ipureintro; exact ⟨rfl, rfl⟩)
      | (iright
         isplitr
         · ipureintro; assumption
         unfold net.rpc.errMsg
         iexists _
         isplitr
         · ipureintro; rfl
         isplitr
         · ipureintro; go_type_set
         iexact HN)

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service
end Perennial
