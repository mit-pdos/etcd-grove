/-
**The real backend instance's laws** (the backend-cmp Probe, 2026-10-30;
`notes/spec-first-study/backend-probe.md`, section 4, sites 18-20): the store's backend-instance
resources (`kbView`, `kbNoCmp`, `kbRegRight`, `kbWT`, `kbRT`) at the real backend `some d`, as
equations, so that a client outside mvcc (the server's boot and snapshot path) does not unfold them.
In a module of their own, so that adding them leaves mvcc's other modules as they were.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BackendBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI backend

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The view of the `Key` bucket at the real backend: the backend's clients' (`bkView`). -/
@[simp] theorem kbView_some (d : KBReal) (γb : GName) (q : Qp) (m : Bucket) :
    kbView (GF := GF) (some d) γb q m = bkView d.γB q m := rfl

/-- The no-compaction token at the real backend: the backend's flag at `0` (`bkNoCmp`). -/
@[simp] theorem kbNoCmp_some (d : KBReal) (γb : GName) :
    kbNoCmp (GF := GF) (some d) γb = bkNoCmp d.γB := rfl

/-- The right to register the store's lock resource at the real backend (`lateReg`). -/
@[simp] theorem kbRegRight_some (d : KBReal) : kbRegRight (GF := GF) (some d) = lateReg d.gx := rfl

/-- A write session's token at the real backend: a write-back's budget (`wbTok`). -/
@[simp] theorem kbWT_some (d : KBReal) : kbWT (GF := GF) (some d) = backend.wbTok d.γB := rfl

/-- A reader's token at the real backend (`bkRTx`). -/
@[simp] theorem kbRT_some (d : KBReal) : kbRT (GF := GF) (some d) = bkRTx d.γB d.P d.be := rfl

end laws

end mvcc
end EtcdGrove
end Perennial
