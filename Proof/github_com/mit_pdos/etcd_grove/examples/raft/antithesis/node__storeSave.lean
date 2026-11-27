/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/node__storeSave.lean`: the hard
state, if any, then the entries, if any, go to the `MemoryStorage` (`SetHardState`, `Append`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__storeSave
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.storeSave.wp_proof (wp_SetHardState : MemoryStorage.SetHardState.spec (GF := GF) (hG := hG))
    (wp_Append : MemoryStorage.Append.spec (GF := GF) (hG := hG)) :
    node.storeSave.spec (GF := GF) (hG := hG) := by
  intro n ms γs h hp oh k old es sl dq hix hlen
  wp_start as ⟨Hst, #Hlock, Hmeta, Hh, Hlog, Hents⟩
  ihave #Hraft : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_auto
  wp_join iprop(memStorMeta ms γs (oh.getD h) ∗ n_ptr ↦ n ∗ n.[H.node, go!"store"] ↦ ms) with [Hmeta Hh n Hst hs]
    as ⟨Hmeta, n, Hst⟩
  · iunfold hsOptRO at Hh
    icases Hh with (⟨-, %Ho⟩ | ⟨%h', ⟨%Hn, -⟩, -⟩)
    · subst Ho
      iframe
    · exact absurd rfl Hn
  · iunfold hsOptRO at Hh
    icases Hh with (⟨%Hn, -⟩ | ⟨%h', ⟨-, %Ho⟩, #Hh⟩)
    · exact absurd Hn Hif
    subst Ho
    wp_apply wp_SetHardState ms γs h hp h' $$ [$Hraft $Hmeta] as Hmeta
    · iunfold hsOpt; iright; iexact Hh
    try wp_auto
    wp_join_done
  iunfold entsPtsZ at Hents
  icases Hents with ⟨%ls, Hsl, #Hb⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  ihave %Hl := BigSepL2.bigSepL2_length $$ Hb
  ihave Hents : entsPtsZ γs.sz sl dq es $$ [Hsl]
  · iunfold entsPtsZ; iexists ls; iframe Hsl Hb
  cases es with
  | nil =>
    have H0 : ¬ sint.Z (W64 0) < sint.Z sl.len := by
      have h1 := Hsll.1; simp only [List.length_nil] at Hl; rw [Hl] at h1; word
    rw [decide_eq_false H0]
    wp_auto
    iapply HΦ
    iframe
    rw [if_pos rfl]
    iempintro
  | cons e r =>
    have H0 : sint.Z (W64 0) < sint.Z sl.len := by
      have h1 := Hsll.1; simp only [List.length_cons] at Hl; rw [Hl] at h1; word
    rw [decide_eq_true H0]
    wp_auto
    wp_apply wp_Append ms γs k old (e :: r) sl dq hix hlen $$ [$Hraft $Hlock $Hlog $Hents] as ⟨Hents, Hlog⟩
    try wp_auto
    iapply HΦ
    iframe
    rw [if_neg (List.cons_ne_nil e r)]
    iexact Hlog

end proof

end AntHarness
end EtcdGrove
end Perennial
