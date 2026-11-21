/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/NewLease.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.NewLease
public import Perennial.Golang.Theory.Chan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.NewLease.wp_proof : lease.NewLease.spec (GF := GF) (hG := hG) := by
  intro id ttl
  wp_start as -
  (try wp_auto)
  wp_apply wp_map_make1 (K := LeaseItem) (V := Unit) as %sm Hsm
  wp_apply +noauto chan.wp_make1 (V := Unit) as %c %γc ⟨#Hch, -, Hown⟩
  -- (prove-ps2-renew) `revokec` a close-once channel: its invariant and its close token
  imod (token_alloc (GF := GF)) with ⟨%γt, Htok⟩
  imod (inv_alloc onceChanN ⊤ (onceChanInv γc γt)) $$ [Hown] with #Hci
  · inext; iunfold onceChanInv; iexists .Idle; dsimp only; iframe Hown
  (try wp_auto)
  irename «$r0» => Hl
  generalize «$r0_ptr» = l at *
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  iStructNamed Hl
  iapply HΦ
  isplitr
  · ipureintro; exact Hnn
  iframe
  iunfold revokeCloser
  iexists γt; iframe Htok
  iunfold onceRecv
  iexists γc; iframe Hch Hci

end proof

end EtcdGrove
end Perennial
