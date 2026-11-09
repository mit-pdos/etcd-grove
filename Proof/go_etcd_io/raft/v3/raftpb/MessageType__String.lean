/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/MessageType__String.lean`, over the trusted model of
protoc-gen-go's `MessageType.String` (`TrustedCode/go_etcd_io/raft/v3/raftpb.lean`, Q9 of
`notes/trace-validation-plan.md`, 2026-11-09): the lookup in `MessageType_name`, which raftpb's
package fact holds read-only, else `strconv.Itoa`. (Until 2026-11-09 a trust-boundary axiom.)
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__String
public import Spec.strconv.Itoa

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

theorem raftpb.MessageType.String.wp_proof
    (hItoa : strconv.Itoa.spec (GF := GF) (hG := hG)) :
    raftpb.MessageType.String.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start as #Hpkg
  ihave #Hsc : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  ihave #Hfact : iprop(∃ m : Loc,
      (globalAddr go_etcd_io.raft.v3.raftpb.MessageType_name ↦□ m : IProp GF) ∗
      m ↦$□ go_etcd_io.raft.v3.raftpb.msgTypeNames) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hfact with ⟨%m, #Hg, #Hm⟩
  -- the trusted model names the translation's type and table by their names
  have hty : (go_etcd_io.raft.v3.raftpb.model.MessageType : go.GoType) =
      go_etcd_io.raft.v3.raftpb.MessageType.ty := by with_unfolding_all rfl
  have hnm : (go_etcd_io.raft.v3.raftpb.model.MessageType_name : GoString) =
      go_etcd_io.raft.v3.raftpb.MessageType_name := by with_unfolding_all rfl
  simp only [hty, hnm]
  wp_auto
  -- the table kept opaque (`wp_auto`'s `simp` would compute its lookups)
  have hS : raftpb.msgTypeString t = match go_etcd_io.raft.v3.raftpb.msgTypeNames !! t with
      | some s => s
      | none => fmtInt (W64 (sint.Z t)) (W64 10) := rfl
  rw [hS]
  generalize go_etcd_io.raft.v3.raftpb.msgTypeNames = M
  cases hk : M !! t with
  | some s =>
    wp_apply (wp_map_lookup2 (K := w32) (V := GoString) go.int32 go.string m M t DFrac.discard)
      $$ Hm as -
    rw [hk]
    simp only [Option.isSome_some, Option.getD_some, _root_.decide_true]
    wp_auto
    iapply HΦ; itrivial
  | none =>
    wp_apply (wp_map_lookup2 (K := w32) (V := GoString) go.int32 go.string m M t DFrac.discard)
      $$ Hm as -
    rw [hk]
    simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
    wp_auto
    wp_apply hItoa $$ Hsc as %str %Hstr
    rw [Hstr]
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial
