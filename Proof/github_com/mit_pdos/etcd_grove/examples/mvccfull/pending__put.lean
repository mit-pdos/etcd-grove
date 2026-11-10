/- Lean-first (no Rocq counterpart). The proof of `pending.put`: the lookup's two arms, each the
insert of `putRec`, then the change appended. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pending__put

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

theorem pending.put.wp_proof : pending.put.spec (GF := GF) (hG := hG) := by
  intro p P k v l
  wp_start as Hp
  iunfold ownPending at Hp
  icases Hp with ⟨%pv, Hp, %Hrev, Hm, Hcs, Hcap⟩
  wp_auto
  wp_apply (wp_map_lookup2 go.string kvRec.ty pv.st' P.st k (DFrac.own 1)) $$ [$Hm] as Hm
  (try wp_auto)
  cases hk : P.st !! k with
  | none =>
    simp only [Option.isSome_none, _root_.decide_false, Bool.false_eq_true, Option.getD_none]
    (try wp_auto)
    wp_apply wp_mapInsert $$ Hm as Hm
    (try wp_auto)
    wp_apply (wp_map_lookup1 go.string kvRec.ty pv.st' _ k (DFrac.own 1)) $$ [$Hm] as Hm
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hcs $Hcap $Hosl] as %cs' ⟨Hcs, Hcap, -⟩
    (try wp_auto)
    iapply HΦ
    iunfold ownPending
    iexists _
    simp only [PendM.put, putRec, hk, Hrev]
    iframe
    ipureintro; rfl
  | some e =>
    simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
    (try wp_auto)
    wp_apply wp_mapInsert $$ Hm as Hm
    (try wp_auto)
    wp_apply (wp_map_lookup1 go.string kvRec.ty pv.st' _ k (DFrac.own 1)) $$ [$Hm] as Hm
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hcs $Hcap $Hosl] as %cs' ⟨Hcs, Hcap, -⟩
    (try wp_auto)
    iapply HΦ
    iunfold ownPending
    iexists _
    simp only [PendM.put, putRec, hk, Hrev]
    iframe
    ipureintro; rfl

end proof

end mvccfull
end EtcdGrove
end Perennial
