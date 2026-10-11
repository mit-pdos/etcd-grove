/-
`(*EtcdServer).apply(es, ep, raftAdvancedC)` (server.go): the apply loop over a batch of
committed entries. Lean-first (no Rocq counterpart); see `InvApplier.lean`, `InvApply.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.apply(es, ep, rac)`, by the apply thread, on a non-empty batch of consecutive
committed entries from `f0` (`entriesFrom`), with the protocol's state `st` processed through
the larger of `ci` and `f0 - 1` (`loopOk`): each entry at or below `ci` is replayed with no
backend writes (`ApplyV2storeOnly`), each above is applied (`ApplyBoth`), and afterwards
`ci` and the processed-through index are both the larger of the old `ci` and the last index
`L`, which it returns with its term. So no entry's writes are applied twice, and none above
`ci` is skipped. -/
abbrev EtcdServer.apply.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (b : GoInterface)
    (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64) (ep : Loc) (cs : Loc)
    (rac : GoChan) (st : ApplyState) (a at0 : w64),
  ms ≠ [] → entriesFrom f0 ms → loopOk γ st (f0 - 1) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ci TM ∗ es ↦*□ ents ∗ entriesAt ents ms ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a at0 ∗ epConfStateAddr ep ↦ cs }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"apply"))
      (Val #es)) (Val #ep)) (Val #rac))
  {{ (appliedt appliedi : w64) (shouldStop : Bool),
      RET (PairV (PairV #appliedt #appliedi) #shouldStop);
      ∃ (st' : ApplyState) (a' at' : w64) (csl : Loc),
        applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' at' ∗
        epConfStateAddr ep ↦ csl ∗
        ⌜(ms.getLast?).map EntryModel.index = some appliedi ∧
          (ms.getLast?).map EntryModel.term = some appliedt ∧
          loopOk γ st' appliedi ∧
          uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z appliedi)⌝ }}

end spec

end EtcdGrove
end Perennial
