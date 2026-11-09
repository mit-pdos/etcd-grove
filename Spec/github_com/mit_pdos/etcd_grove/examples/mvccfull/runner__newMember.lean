/- Lean-first (no Rocq counterpart).

`x.newMember(id, path)` (`examples/mvccfull/mvccfull.go`): a member over the fresh file `path`
(`fileHolds path ∅`): its struct, its hook closure (`hookOk`: it saves the index being applied when
above the saved one), the bounds at the empty store's (`1`, `1`, `-1`, `-1`), its ghost names, and
`open` (at the empty history, `mvccImage_fresh.law`). Afterwards it is a member between operations
(`memW`) at no operation of any log, the writer holding every share; no streams; its `regs` counter
in an invariant.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev runner.newMember.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] (x : Loc) (ks : List GoString)
    (cfg : Config) (wr : List w64) (h : Loc) (γh : HistNames) (id : w64) (path : GoString),
  0 ≤ sint.Z id → sint.Z id ≤ 2 → backend.dbOpenOk → ckptEffectsOk →
  sint.Z (limOf cfg) ≤ 2 ^ 57 → batchLimitOk (cblOf cfg) →
  {{ writerCtx (GF := GF) x ks cfg wr h γh ∗
      □ (∀ (γB : backend.BNames) (P : backend.BParams) (b' : Loc), keySized γB P b') ∗
      envVerifyOff ∗ threadTok ∗ histRd h γh ∗ monoListLbOwn γh.l hist0 ∗ backend.fileHolds path ∅ }}
    (App (App (x @!! go.GoType.PointerType runner.ty @!! go!"newMember") (Val #id)) (Val #path))
  {{ (mp : Loc), RET #mp; threadTok ∗ histRd h γh ∗
      ∃ (m : MemberNames) (f : GoFunc) (v : MemS) (k : Nat),
        ⌜v.ops = 0 ∧ v.path = path ∧ (sint.Z cfg.Ops').toNat ≤ k⌝ ∗
        (∀ ops : List OpM, memW ks γh ops (sint.nat id) mp m f v 1 1 mvccReaderN k) ∗
        mF go!"streams" mp ↦ (slice.nil : GoSlice) ∗ ctrInv (sCtrN .@ "regs") (mF go!"regs" mp) }}

end spec

end mvccfull
end EtcdGrove
end Perennial
