/-
Package initialization of `go_etcd_io.etcd.api.v3.etcdserverpb`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`etcdserverpbInit`, `cache/v3/Base.lean`): the sort enumerations' name maps. Its
initializer allocates and sets the translated gRPC service descriptors (`KV_ServiceDesc`, ...:
`grpc.ServiceDesc` literals), initializes its imports and runs its other variables' untranslated
initializers (the generated protobuf descriptors and enum maps), which the trust-boundary axiom
`opaqueInitsOk` says run. (const-inits, 2026-11-19) The two sort enumerations' name maps the fact
reads (`RangeRequest_SortOrder_name`, `RangeRequest_SortTarget_name`: `map[int32]string` literals,
`rpc.pb.go`) are translated and set; until then the trust-boundary axioms `<X>_init`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Proof.go_etcd_io.etcd.api.v3.authpb.Init
public import Proof.go_etcd_io.etcd.api.v3.membershippb.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.google_golang_org.grpc.Init
public import Proof.google_golang_org.protobuf.runtime.protoimpl.Init
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace go_etcd_io.etcd.api.v3.etcdserverpb
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.api.v3.etcdserverpb`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0», init.«1», init.«2»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end go_etcd_io.etcd.api.v3.etcdserverpb
end opaqueInits

/-- A small 64-bit literal's value as a signed natural (the descriptors' slice indices). -/
theorem EtcdGrove.sint_nat_ofNat64 (n : Nat) (h : n < 2 ^ 63) : sint.nat (BitVec.ofNat 64 n) = n := by
  simp [sint.nat, BitVec.toInt]; omega

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

namespace go_etcd_io.etcd.api.v3.etcdserverpb

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) Auth_ServiceDesc _ as HAuth_ServiceDesc
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) Maintenance_ServiceDesc _ as HMaintenance_ServiceDesc
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) Cluster_ServiceDesc _ as HCluster_ServiceDesc
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) Lease_ServiceDesc _ as HLease_ServiceDesc
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) Watch_ServiceDesc _ as HWatch_ServiceDesc
  wp_apply wp_GlobalAlloc (V := google_golang_org.grpc.ServiceDesc) KV_ServiceDesc _ as HKV_ServiceDesc
  wp_apply wp_GlobalAlloc (V := Loc) RangeRequest_SortTarget_name _ as HRangeRequest_SortTarget_name
  wp_apply wp_GlobalAlloc (V := Loc) RangeRequest_SortOrder_name _ as HRangeRequest_SortOrder_name
  wp_apply (_root_.Perennial.google_golang_org.grpc.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.context _root_.Perennial.context.initialize'
      EtcdGrove.ExternalInit.context _root_.Perennial.context.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.mvccpb.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.authpb.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.membershippb.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.google_golang_org.protobuf.runtime.protoimpl.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of RangeRequest_SortOrder_name))
  try wp_auto
  wp_apply (wp_map_make1 (K := w32) (V := GoString) go.int32 go.string) as %mHso Hso
  try wp_auto
  repeat (wp_apply (wp_mapInsert (K := w32) (V := GoString) go.int32) $$ Hso as Hso; try wp_auto)
  -- translated initializer of RangeRequest_SortTarget_name))
  try wp_auto
  wp_apply (wp_map_make1 (K := w32) (V := GoString) go.int32 go.string) as %mHst Hst
  try wp_auto
  repeat (wp_apply (wp_mapInsert (K := w32) (V := GoString) go.int32) $$ Hst as Hst; try wp_auto)
  -- translated initializer of KV_ServiceDesc))
  -- translated initializer of Watch_ServiceDesc))
  -- translated initializer of Lease_ServiceDesc))
  -- translated initializer of Cluster_ServiceDesc))
  -- translated initializer of Maintenance_ServiceDesc))
  -- translated initializer of Auth_ServiceDesc))
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pKVm ⟨SKVm, -⟩; try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pKVs ⟨SKVs, -⟩; try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pWm ⟨SWm, -⟩; try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pWs ⟨SWs, -⟩; try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pLm ⟨SLm, -⟩; try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pLs ⟨SLs, -⟩; try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pCm ⟨SCm, -⟩; try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pCs ⟨SCs, -⟩; try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pMm ⟨SMm, -⟩; try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pMs ⟨SMs, -⟩; try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pAm ⟨SAm, -⟩; try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %pAs ⟨SAs, -⟩; try wp_auto
  try wp_auto
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  wp_apply (initFuncsOk init.«1» (by mem_tac))
  wp_apply (initFuncsOk init.«2» (by mem_tac))
  ipersist SKVm
  ipersist SKVs
  ipersist SWm
  ipersist SWs
  ipersist SLm
  ipersist SLs
  ipersist SCm
  ipersist SCs
  ipersist SMm
  ipersist SMs
  ipersist SAm
  ipersist SAs
  ipersist HKV_ServiceDesc
  ipersist HWatch_ServiceDesc
  ipersist HLease_ServiceDesc
  ipersist HCluster_ServiceDesc
  ipersist HMaintenance_ServiceDesc
  ipersist HAuth_ServiceDesc
  iStructNamedSuffix HKV_ServiceDesc "KV"
  iStructNamedSuffix HWatch_ServiceDesc "Watch"
  iStructNamedSuffix HLease_ServiceDesc "Lease"
  iStructNamedSuffix HCluster_ServiceDesc "Cluster"
  iStructNamedSuffix HMaintenance_ServiceDesc "Maintenance"
  iStructNamedSuffix HAuth_ServiceDesc "Auth"
  ipersist HRangeRequest_SortOrder_name
  ipersist HRangeRequest_SortTarget_name
  ipersist Hso
  ipersist Hst
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold go_etcd_io.etcd.cache.v3.etcdserverpbInit go_etcd_io.etcd.cache.v3.etcdserverpbDescs go_etcd_io.etcd.cache.v3.pbDescIs
  isplitl []
  · iexists _, _; iframe HRangeRequest_SortOrder_name Hso; ipureintro; intro k; simp only [GMap.lookup_insert_eq_iff, GMap.lookup_empty]; by_cases hk : k = W32 0 ∨ k = W32 1 ∨ k = W32 2; (· rcases hk with rfl | rfl | rfl <;> simp (config := {decide := true})); (· have hr : ¬ (0 ≤ sint.Z k ∧ sint.Z k ≤ 2) := fun hr => hk (by word); simp only [hr, iff_false, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]; rw [if_neg (show ¬(W32 2 = k) from fun h => hk (by subst h; simp)), if_neg (show ¬(W32 1 = k) from fun h => hk (by subst h; simp)), if_neg (show ¬(W32 0 = k) from fun h => hk (by subst h; simp))])
  isplitl []
  · iexists _, _; iframe HRangeRequest_SortTarget_name Hst; ipureintro; intro k; simp only [GMap.lookup_insert_eq_iff, GMap.lookup_empty]; by_cases hk : k = W32 0 ∨ k = W32 1 ∨ k = W32 2 ∨ k = W32 3 ∨ k = W32 4; (· rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true})); (· have hr : ¬ (0 ≤ sint.Z k ∧ sint.Z k ≤ 4) := fun hr => hk (by word); simp only [hr, iff_false, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]; rw [if_neg (show ¬(W32 4 = k) from fun h => hk (by subst h; simp)), if_neg (show ¬(W32 3 = k) from fun h => hk (by subst h; simp)), if_neg (show ¬(W32 2 = k) from fun h => hk (by subst h; simp)), if_neg (show ¬(W32 1 = k) from fun h => hk (by subst h; simp)), if_neg (show ¬(W32 0 = k) from fun h => hk (by subst h; simp))])
  iframe #
  repeat (first | (isplitl []; · (ipureintro; simp (config := {decide := true}) [go.arrayLiteralSize, EtcdGrove.sint_nat_ofNat64])) | (ipureintro; simp (config := {decide := true}) [go.arrayLiteralSize, EtcdGrove.sint_nat_ofNat64]))

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.api.v3.etcdserverpb

end init

end Perennial
