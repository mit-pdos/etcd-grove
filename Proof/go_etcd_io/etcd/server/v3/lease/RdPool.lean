/-
**The lessor's reader pool, made** (the lease-src plan, 2026-11-02; `notes/lease-src-plan.md`).
Lean-first (no Rocq counterpart).

`lessorRdPool_init`: the pool (`lessorRdPool`, `InvLessor.lean`) of `n` reader slots of the lessor's
lock, enough for every thread but one. The lessor's lock is the lease package's, so this is the
owner turning its stock of slots into a pool (`notes/bounds-plan.md`; `etc/bounds-allow.txt`):
`NewServer` gives it the `2^30 - 2` slots of `NewLessor`'s it does not keep.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The lessor's reader pool, from `n` reader slots** (enough for every thread but one). -/
theorem lessorRdPool_init (γl : GName) (E : CoPset) (n : Nat) (Hn : threadBound GF ≤ n + 1) :
    ([∗list] _x ∈ List.replicate n (), lessorRdOf (GF := GF) γl) ⊢ |={E}=> lessorRdPool γl := by
  iintro Hs
  imod threadPool.init lessorPoolN (lessorRdOf γl) E n Hn $$ Hs with ⟨%γp, #Hp⟩
  imodintro
  unfold lessorRdPool
  iexists γp
  iexact Hp

end proof

end lease
end EtcdGrove
end Perennial
