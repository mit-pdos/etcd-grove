/-
`u.ID()` on a `UUID` value returns some `uint32` (`github_com.google.uuid.UUID.ID.spec`,
`Dsverify/Proof/github_com/imdea_software/swiftpaxos/lib/LibSpecs.lean`), **proved** from uuid's
translation (its model `models/uuid`, v1.3.1's `dce.go` verbatim, dsv-retire-2, #49 step 2): `func
(uuid UUID) ID() uint32 { return binary.BigEndian.Uint32(uuid[0:4]) }`: a `UUID` is a `[16]byte`
value, copied to a local, so the slice is in range; `BigEndian` is `encoding/binary`'s initialized
global (from `isPkgInit uuid`, the precondition it gained then: ledger `notes/specs-only/ledger.md`,
2026-11-25). A trust-boundary axiom from dsv-fix4 (mit-pdos/etcd-grove#49 fix 4) until dsv-retire-2.
Review of the axiom: `notes/axiom-review/dsv-fix4/google-uuid.md`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.LibSpecs
public import Dsverify.Proof.github_com.google.uuid.Base
public import Perennial.Proof.encoding.binary.Results
public import Perennial.Proof.crypto.sha1.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- `u.ID()`: some `uint32` (the file header). -/
theorem github_com.google.uuid.UUID.ID.wp_proof [github_com.google.uuid.Assumptions] :
    github_com.google.uuid.UUID.ID.spec (GF := GF) := by
  intro u
  wp_start as #Hpkg
  ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  wp_auto
  obtain ⟨vs⟩ := u
  ihave %Hlen := array_len _ _ _ _ $$ uuid
  have hsplit := array_split (V := w8) (GF := GF) (W64 4) uuid_ptr (DFrac.own 1) 16
    (array.mk 16 vs) ⟨by decide, by decide⟩
  icases hsplit.1 $$ uuid with ⟨Ha1, -⟩
  ihave Hs := crypto.sha1.slice_of_array_int _ 4 ⟨by omega, by omega⟩ _ _ (W64 16 - W64 0)
    (by decide) $$ [Ha1]
  · simp only [show sint.Z (W64 4) = 4 by rfl, show sint.nat (W64 4) = 4 by rfl]
    rw [go.arrayIndexRef_0]
    iexact Ha1
  wp_apply (encoding.binary.wp_BigEndian_Uint32 _ (vs.take 4) _ [] (by simp; omega)) $$ [Hs] as -
  · iframe Hbin; rw [List.append_nil]; iexact Hs
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
