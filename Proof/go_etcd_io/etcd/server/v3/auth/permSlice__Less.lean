/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/permSlice__Less.lean`. Lean-first (no Rocq counterpart; PR
etcd#21845, `pr-verify/etcd-21845`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.permSlice__Less
public import Perennial.Proof.bytes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth go_etcd_io.etcd.api.v3 auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.permSlice.Less.wp_proof : auth.permSlice.Less.spec (GF := GF) (hG := hG) := by
  intro sl l i j a b
  wp_start as ⟨Hps, %Hij⟩
  iunfold ownPerms at Hps
  icases Hps with ⟨Hs, Hms⟩
  ihave #Hbytes : isPkgInit (PROP := IProp GF) pkg_id.bytes $$ []
  · iPkgInit
  wp_auto
  obtain ⟨hi0, hj0, ha, hb⟩ := Hij
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  simp only [List.length_map] at Hl
  have hilt : sint.nat i < l.length := (List.getElem?_eq_some_iff.1 ha).1
  have hjlt : sint.nat j < l.length := (List.getElem?_eq_some_iff.1 hb).1
  have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by have := Hl.1; refine ⟨hi0, ?_⟩; word
  have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by have := Hl.1; refine ⟨hj0, ?_⟩; word
  try simp only [Hbi, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z i) _ (DFrac.own 1) a.1 hi0 $$ [Hs] as Hs
  · iframe; ipureintro; rw [List.getElem?_map]; exact congrArg (Option.map Prod.fst) ha
  icases auth.ownPerms_acc l (sint.nat i) a ha $$ Hms with ⟨Ha, Hclose⟩
  iunfold ownPerm at Ha
  icases Ha with ⟨%va, Hva, %Hpta, #Hka, #Hrea⟩
  wp_auto
  ihave Hms := Hclose $$ [Hva]
  · iunfold ownPerm; iexists va; iframe; iframe #; ipureintro; exact Hpta
  try simp only [Hbj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index sl (sint.Z j) _ (DFrac.own 1) b.1 hj0 $$ [Hs] as Hs
  · iframe; ipureintro; rw [List.getElem?_map]; exact congrArg (Option.map Prod.fst) hb
  icases auth.ownPerms_acc l (sint.nat j) b hb $$ Hms with ⟨Hb, Hclose⟩
  iunfold ownPerm at Hb
  icases Hb with ⟨%vb, Hvb, %Hptb, #Hkb, #Hreb⟩
  wp_auto
  ihave Hms := Hclose $$ [Hvb]
  · iunfold ownPerm; iexists vb; iframe; iframe #; ipureintro; exact Hptb
  wp_apply (bytes.wp_Compare _ _ DFrac.discard DFrac.discard a.2.key b.2.key) $$ [$Hka $Hkb]
    as ⟨-, -⟩
  rw [auth.compareResult_neg,
    show decide (go.GoStringLt a.2.key b.2.key) = decide (keyLt a.2 b.2) from rfl]
  iapply HΦ
  iunfold ownPerms
  iframe

end proof

end EtcdGrove
end Perennial
