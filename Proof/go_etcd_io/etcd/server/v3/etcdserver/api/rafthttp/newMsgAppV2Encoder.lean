/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/newMsgAppV2Encoder.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newMsgAppV2Encoder

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.newMsgAppV2Encoder.wp_proof :
    rafthttp.newMsgAppV2Encoder.spec (GF := GF) (hG := hG) := by
  intro wi fs
  wp_start as %Hfs
  wp_auto
  wp_apply (wp_make_bytes_abs (W64 1048576) (by decide)) as %buf ⟨%zs, Hbufs, Hbufc, %Hbl⟩
  ihave %Hbl2 := ownSlice_len _ _ _ $$ Hbufs
  wp_apply (wp_slice_make2 (V := w8) (W64 8)) as %s8 ⟨Hs8s, Hs8c⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %s1 ⟨Hs1s, Hs1c⟩
  · ipureintro; decide
  (try wp_auto)
  wp_alloc e as He
  iStructNamed He
  ipersist w; ipersist fs; ipersist buf; ipersist uint64buf; ipersist uint8buf
  wp_auto
  iapply HΦ
  iunfold v2EncOwn
  iexists buf, s8, s1, zs, _, _
  iframe Hbufs Hbufc Hs8s Hs1s
  iframe #
  simp only [show (W64 0 : w64) = 0 from rfl]
  iframe term index
  ipureintro
  refine ⟨Hfs, ?_, by simp, by simp⟩
  unfold v2BufSize
  have h1 : sint.nat buf.len = 1048576 := by
    rw [← Hbl2.1, Hbl]; rfl
  have h3 := Int.toNat_of_nonneg Hbl2.2
  unfold sint.nat at h1
  show sint.Z buf.len = 1048576
  rw [← h3, h1]; rfl

end proof

end EtcdGrove
end Perennial
