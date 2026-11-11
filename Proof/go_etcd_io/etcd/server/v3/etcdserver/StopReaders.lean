/-
**The stop's serving readers from the stocks `NewServer` hands out** (R2c review F3, 2026-11-06;
round 2's N3: its own module, so that the stop's slot `StopApi` does not import the watch server's
vocabulary). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRestart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvWatchBuilt
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServe

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section readers
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- `n ≥ 1` single reader tokens of the store are `n` of them (`mvccReaders_split.law`). -/
theorem mvccReaders_ofRep (hRS : mvcc.api.mvccReaders_split.law (GF := GF))
    (γ : mvcc.api.MvccName) (n : Nat) (hn : 1 ≤ n) :
    ([∗list] _x ∈ List.replicate n (), mvcc.api.mvccReaders (GF := GF) γ 1) ⊢
      mvcc.api.mvccReaders γ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction m with
  | zero =>
    rw [List.replicate_succ]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, -⟩
    iexact H1
  | succ m ih =>
    iintro H
    rw [List.replicate_succ]
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
    iapply (hRS γ (m + 1) 1).2
    iframe H1
    iapply ih $$ H

/-- **The stop's serving readers** (`srvStopReaders`) from `NewServer`'s 64 reader tokens, its
watch service's 64 (`srvWatchReaders`' tokens, `srvWatchReaders_readers`) and (per-type stage B2,
2026-11-11) the gRPC run pool's raw stock, a member that never served (`srvServeStock`'s
`srvRevokePoolN` tokens; its `bemu` slots, `lgMu` slots and the built part are dropped), joined by
the API's `mvccReaders_split.law`. -/
theorem srvStopReaders_intro (hRS : mvcc.api.mvccReaders_split.law (GF := GF)) (s : Loc)
    (E : apply.AEnv GF) :
    mvcc.api.mvccReaders E.γ 64 ∗ srvWatchReaders s E 64 ∗ srvServeStock s E ⊢
      srvStopReaders (GF := GF) E := by
  unfold srvStopReaders
  iintro ⟨Hsts, HWR, Hstk⟩
  ihave Hw := srvWatchReaders_readers s E 64 $$ HWR
  iunfold srvServeStock at Hstk
  icases Hstk with ⟨-, Hp, -, -⟩
  ihave Hp := replicate_mono iprop(mvcc.api.mvccReaders E.γ 1 ∗ srvBemuReader s)
    (mvcc.api.mvccReaders E.γ 1) srvRevokePoolN (by iintro ⟨H, -⟩; iexact H) $$ Hp
  ihave Hp := mvccReaders_ofRep hRS E.γ srvRevokePoolN
    (by simp only [srvRevokePoolN, backend.rdPoolN]; omega) $$ Hp
  iapply (hRS E.γ srvRevokePoolN (64 + 64)).2
  iframe Hp
  iapply (hRS E.γ 64 64).2
  iframe Hsts Hw

end readers

end EtcdGrove
end Perennial
