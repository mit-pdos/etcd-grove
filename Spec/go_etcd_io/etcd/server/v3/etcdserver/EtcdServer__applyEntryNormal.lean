/-
`(*EtcdServer).applyEntryNormal(e, shouldApplyV3)` (server.go): one normal entry, and the
consistent index after it. Lean-first (no Rocq counterpart); see `InvApplier.lean`,
`InvApply.lean`.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.applyEntryNormal(e, v3)`, by the apply thread (protocol state `st`, out of flight).
With `v3` (`ApplyBoth`: the entry `i = p + 1`, above `ci`, whose index and term are the
applying index): the entry is applied (through `apply.Apply`, or not at all if it has no data)
and, after it, `ci` and the processed-through index are both `i` (the post-lock hook set `ci`
if the entry had writes; else the deferred update does, outside the lock). Without `v3` (an
entry at or below `ci`, replayed): nothing is written to the backend and the state is
unchanged. -/
abbrev EtcdServer.applyEntryNormal.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (b : GoInterface)
    (e : Loc) (m : EntryModel) (st : ApplyState) (v3 : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ci TM ∗ entryAt e m ∗ applyThread γ st ∗ applyBackend γ ci b ∗
      ⌜st.pending = false⌝ ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ⌜m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
       else iprop(True)) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntryNormal"))
      (Val #e)) (Val #v3))
  {{ RET #(); applyBackend γ ci b ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩)
       else applyThread γ st) }}

end spec

end EtcdGrove
end Perennial
