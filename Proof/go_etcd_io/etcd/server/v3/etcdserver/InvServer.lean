/-
The etcd server's state as the apply thread sees it (`server/v3/etcdserver/server.go`): the
shared vocabulary of `Spec/EtcdServer__*.lean`. Lean-first (no Rocq counterpart); the
protocol is `InvApply.lean`.

- `isServerCI s γ ci` (persistent): `s.consistIndex` is the `*consistentIndex` `ci`, with the
  protocol's invariant.
- `applyBackend γ ci b`: the apply thread's half of `ci.be` (the backend `b`) and the
  backend's read contract for the protocol's read view (`readView`).
- `hookSpec γ ci TM f` (persistent): `f` is the backend's post-lock hook
  (`getTxPostLockInsideApplyHook`): called under the batch lock (`batchLockInv γ TM`), during
  the application of the entry `i = p + 1` (whose index is the applying index), it sets the
  consistent index to `i` and leaves the entry's writes in flight; it gives back the lock's
  resources but its token (`hookDone`), which `writes_done` returns.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__UnsafeConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetConsistentIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.etcdserver

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `s.consistIndex`. -/
abbrev srvCIAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"consistIndex" s

end addrs

section typeRepr
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `TypeRepr` of the structs the apply thread reads fields of (named and underlying types),
straight from their `TypeAssumptions` (as `Cache/InvStore.lean` does for the cache's
messages). Without these, the `StructFieldRef` step finds `TypeRepr` through the struct's
`IntoValTyped` instance, which is built from those of every field, and the server's fields of
axiomatized types (`raft.Node`, `auth.AuthStore`, ...) have `sorry` instances. -/
instance (priority := high) etcdServer_typeRepr : TypeRepr EtcdServer.ty EtcdServer :=
  go.type_repr_underlying (u := EtcdServer.underlying)
instance (priority := high) etcdServer_typeRepr_u : TypeRepr EtcdServer.underlying EtcdServer :=
  go.type_repr_underlying (u := EtcdServer.underlying)
instance (priority := high) serverConfig_typeRepr :
    TypeRepr go_etcd_io.etcd.server.v3.config.ServerConfig.ty
      go_etcd_io.etcd.server.v3.config.ServerConfig :=
  go.type_repr_underlying (u := go_etcd_io.etcd.server.v3.config.ServerConfig.underlying)
instance (priority := high) serverConfig_typeRepr_u :
    TypeRepr go_etcd_io.etcd.server.v3.config.ServerConfig.underlying
      go_etcd_io.etcd.server.v3.config.ServerConfig :=
  go.type_repr_underlying (u := go_etcd_io.etcd.server.v3.config.ServerConfig.underlying)
instance (priority := high) etcdProgress_typeRepr : TypeRepr etcdProgress.ty etcdProgress :=
  go.type_repr_underlying (u := etcdProgress.underlying)
instance (priority := high) etcdProgress_typeRepr_u : TypeRepr etcdProgress.underlying etcdProgress :=
  go.type_repr_underlying (u := etcdProgress.underlying)
instance (priority := high) toApply_typeRepr : TypeRepr toApply.ty toApply :=
  go.type_repr_underlying (u := toApply.underlying)
instance (priority := high) toApply_typeRepr_u : TypeRepr toApply.underlying toApply :=
  go.type_repr_underlying (u := toApply.underlying)

end typeRepr

/-- The interface value of a `*consistentIndex`. -/
abbrev ciIface [FfiSyntax] [GoGlobalContext] (ci : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType consistentIndex.ty) #ci

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `s.consistIndex` is the consistent index `ci`, with the protocol's invariant
(persistent). -/
def isServerCI (s : Loc) (γ : ApplyNames) (ci : Loc) : IProp GF :=
  iprop(srvCIAddr s ↦□ ciIface ci ∗ isCI ci γ.ci ∗ inv applyN (consInv γ))

instance isServerCI_persistent (s : Loc) (γ : ApplyNames) (ci : Loc) :
    Persistent (isServerCI (GF := GF) s γ ci) := by
  unfold isServerCI; infer_instance

/-- The apply thread's backend: its half of `ci.be`, the backend `b`, whose read view is the
protocol's. -/
def applyBackend (γ : ApplyNames) (ci : Loc) (b : GoInterface) : IProp GF :=
  iprop(ciOwner ci b ∗ isMetaBackend b (⊤ \ ↑applyN) (readView γ))

/-- The batch lock's resources but its token: what the post-lock hook leaves, the entry's
writes in flight. -/
def hookDone (γ : ApplyNames) (TM : MetaCI → IProp GF) : IProp GF :=
  iprop(∃ mm : MetaCI, ghostVar γ.mt (1 : Qp).half mm.1 ∗ TM mm)

/-- The post-lock hook's contract (persistent). -/
def hookSpec (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (f : val) : IProp GF :=
  iprop(∀ (st : ApplyState) (i t : w64) (b : GoInterface),
    {{ batchLockInv γ TM ∗ applyThread γ st ∗ ciApplying ci i t ∗ applyBackend γ ci b ∗
        ⌜st.pending = false ∧ i = st.p + 1 ∧ uint.Z st.p < uint.Z i ∧
          uint.Z (ciEff γ st.k) < uint.Z i⌝ }}
      (App (Val f) (Val #()))
    {{ RET #(); hookDone γ TM ∗ applyThread γ { st with k := i, pending := true } ∗
        ciApplying ci i t ∗ applyBackend γ ci b }})

instance hookSpec_persistent (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (f : val) :
    Persistent (hookSpec (GF := GF) γ ci TM f) := by
  unfold hookSpec; infer_instance

/-- The protocol's state after reading `ci` (`ConsistentIndex`/`UnsafeConsistentIndex`):
loaded if it was 0. -/
def stLoaded (γ : ApplyNames) (st : ApplyState) : ApplyState :=
  if st.k = W64 0 then { st with k := γ.m0.1 } else st

/-- Reading `ci` through `ConsistentIndex`/`UnsafeConsistentIndex` (by the apply thread,
outside an entry's flight): the update their specs take. It returns `ciEff γ st.k`, and
loads `ci` if it was 0. -/
theorem ci_get_au (γ : ApplyNames) (ci : Loc) (b : GoInterface) (st : ApplyState)
    (hp : st.pending = false) (Φ : val → IProp GF) :
    inv applyN (consInv γ) ⊢ applyThread γ st -∗
      (applyThread γ (stLoaded γ st) -∗ ciOwner ci b -∗ Φ #(ciEff γ st.k)) -∗
      |={⊤ \ ↑ciN, ∅}=> ∃ k : w64, ciIdx γ.ci k ∗ (ciIdx γ.ci k ={∅, ⊤ \ ↑ciN}=∗
        if k = W64 0 then
          readCIAU (⊤ \ ↑applyN) (readView γ) (fun m => iprop(|={⊤ \ ↑ciN, ∅}=> ∃ k' : w64,
            ciIdx γ.ci k' ∗ (ciIdx γ.ci m.1 ={∅, ⊤ \ ↑ciN}=∗ (ciOwner ci b -∗ Φ #m.1))))
        else (ciOwner ci b -∗ Φ #k)) := by
  iintro #Hinv Hst HΦ
  iapply ci_read_au γ st _ $$ Hinv Hst
  iintro Hst
  by_cases hk : st.k = W64 0
  · simp only [stLoaded, ciEff, hk, ↓reduceIte]
    iapply read_ci_au γ st hk $$ Hinv Hst
    iintro Hst
    rw [loadedMeta_fst]
    iapply ci_load_store_au γ st hk hp $$ Hinv Hst
    iintro Hst
    iapply HΦ $$ Hst
  · simp only [stLoaded, ciEff, hk, ↓reduceIte]
    iapply HΦ $$ Hst

/-! ## The consistent index's operations in the protocol's terms

Specs derived from the consistent index's specs (taken as hypotheses), with the protocol's
updates (`InvApply.lean`) at their linearization points. They take the continuation without
a later (as Perennial's `sync/atomic` specs do, and unlike a Hoare triple): the consistent
index's specs give it to the caller inside their atomic updates, where no step strips one. -/

section derived
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `ci.UnsafeConsistentIndex()` by the apply thread: `ciEff`, loading `ci` if it was 0. -/
theorem wp_ci_unsafeGet (hU : consistentIndex.UnsafeConsistentIndex.spec (GF := GF) (hG := hG))
    (γ : ApplyNames) (ci : Loc) (b : GoInterface) (st : ApplyState) (hp : st.pending = false) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI ci γ.ci ∗ inv applyN (consInv γ) ∗ applyThread γ st ∗ applyBackend γ ci b) -∗
      (applyThread γ (stLoaded γ st) ∗ applyBackend γ ci b -∗ Φ #(ciEff γ st.k)) -∗
      WP (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"UnsafeConsistentIndex"))
        (Val #())) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hci, #Hinv, Hst, Hbe⟩ HΦ
  iunfold applyBackend at Hbe
  icases Hbe with ⟨Hown, #Hmb⟩
  iapply (hU ci γ.ci b (⊤ \ ↑applyN) (readView γ)) $$ [Hown] [HΦ Hst]
  · iframe Hpkg Hci Hown Hmb
  iapply ci_get_au γ ci b st hp $$ Hinv Hst
  iintro Hst Hown
  iapply HΦ
  iframe Hst
  iunfold applyBackend
  iframe Hown Hmb

/-- `ci.ConsistentIndex()` by the apply thread: `ciEff`, loading `ci` if it was 0. -/
theorem wp_ci_get (hC : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (γ : ApplyNames) (ci : Loc) (b : GoInterface) (st : ApplyState) (hp : st.pending = false) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI ci γ.ci ∗ inv applyN (consInv γ) ∗ applyThread γ st ∗ applyBackend γ ci b) -∗
      (applyThread γ (stLoaded γ st) ∗ applyBackend γ ci b -∗ Φ #(ciEff γ st.k)) -∗
      WP (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"ConsistentIndex"))
        (Val #())) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hci, #Hinv, Hst, Hbe⟩ HΦ
  iunfold applyBackend at Hbe
  icases Hbe with ⟨Hown, #Hmb⟩
  iapply (hC ci γ.ci b (⊤ \ ↑applyN) (readView γ)) $$ [Hown] [HΦ Hst]
  · iframe Hpkg Hci Hown Hmb
  iapply ci_get_au γ ci b st hp $$ Hinv Hst
  iintro Hst Hown
  iapply HΦ
  iframe Hst
  iunfold applyBackend
  iframe Hown Hmb

/-- The post-lock hook's `ci.SetConsistentIndex(i, t)`, holding the batch lock's token, for
the entry `i = p + 1`: its writes are now in flight. -/
theorem wp_ci_hookSet (hS : consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG))
    (γ : ApplyNames) (ci : Loc) (st : ApplyState) (i t : w64) (hp : st.pending = false)
    (hi : i = st.p + 1) (hlt : uint.Z st.p < uint.Z i) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI ci γ.ci ∗ inv applyN (consInv γ) ∗ applyThread γ st ∗ token γ.pend) -∗
      (applyThread γ { st with k := i, pending := true } -∗ Φ #()) -∗
      WP (App (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"SetConsistentIndex"))
        (Val #i)) (Val #t)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hci, #Hinv, Hst, Htok⟩ HΦ
  iapply (hS ci γ.ci i t) $$ [] [HΦ Hst Htok]
  · iframe Hpkg Hci
  iapply hook_set_au γ st i _ hp hi hlt $$ Hinv Hst Htok
  iintro Hst
  iapply HΦ $$ Hst

/-- The deferred `ci.SetConsistentIndex(i, t)` of `applyEntryNormal`, outside the batch lock,
for a processed entry `i` above `ci`. -/
theorem wp_ci_advance (hS : consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG))
    (γ : ApplyNames) (ci : Loc) (st : ApplyState) (i t : w64) (hp : st.pending = false)
    (hle : uint.Z i ≤ uint.Z st.p) (hlt : uint.Z (ciEff γ st.k) < uint.Z i) :
    ⊢ ∀ Φ : val → IProp GF,
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗
      isCI ci γ.ci ∗ inv applyN (consInv γ) ∗ applyThread γ st) -∗
      (applyThread γ { st with k := i } -∗ Φ #()) -∗
      WP (App (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"SetConsistentIndex"))
        (Val #i)) (Val #t)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, #Hci, #Hinv, Hst⟩ HΦ
  iapply (hS ci γ.ci i t) $$ [] [HΦ Hst]
  · iframe Hpkg Hci
  iapply ci_advance_au γ st i hp hle hlt _ $$ Hinv Hst
  iintro Hst
  iapply HΦ $$ Hst

end derived

end defs

end EtcdGrove
end Perennial
