-- The copy for the part `KvRaft/` of `Net/ManualProof/net.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The instances goose's proofgen emits for a translated struct (typed points-to, field access,
`IntoValTyped`), stated for the struct whose layout is trusted in `Net/TrustedCode/net.lean`:
`UDPConn` (lean's trusted UDP, `notes/net-udp.md`), of which goose emits none. Proved, from the
hand-stated field facts `net.UdpFieldAssumptions` (an instance hypothesis). (The TCP types are
translated since the Go-model overlays, S6, so goose emits theirs.)
-/
module

public import Perennial.Proof.ProofPrelude
public import GooseLang.Ext.Net.Impl
public import Perennial.Golang.Theory
public import KvRaft.Code.net

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace net

open Iris Iris.BI

section udp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [udp_field_sem : net.UdpFieldAssumptions]

/-- `Addr.ty` is the named type of the trusted layout's address field (stated in `TrustedCode`,
which `Code.net`'s `Addr.ty` cannot be). -/
theorem Addr_ty_eq : Addr.ty = go.GoType.Named go!"net.Addr" [] := by unfold Addr.ty; rfl

instance Addr_named_underlying :
    go.UnderlyingDirectedEq (go.GoType.Named go!"net.Addr" []) Addr.underlying := by
  rw [← Addr_ty_eq]; infer_instance

instance UDPConn_typed_pointsto : TypedPointsto (GF := GF) UDPConn where
  typedPointstoDef l v dq := iprop(
    "uid" ∷ typedPointsto (structFieldRef UDPConn go!"uid" l) v.id' dq ∗
    "laddr" ∷ typedPointsto (structFieldRef UDPConn go!"laddr" l) v.laddr' dq ∗
    "net" ∷ typedPointsto (structFieldRef UDPConn go!"net" l) v.net' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance UDPConn_access_load_uid (l : Loc) (v : UDPConn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef UDPConn go!"uid" l) v.id' dq)
      (typedPointsto (structFieldRef UDPConn go!"uid" l) v.id' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance UDPConn_access_store_uid (l : Loc) (v : UDPConn) (id' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef UDPConn go!"uid" l) v.id' (DFrac.own 1))
      (typedPointsto (structFieldRef UDPConn go!"uid" l) id' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with id' := id' } : UDPConn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance UDPConn_access_load_laddr (l : Loc) (v : UDPConn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef UDPConn go!"laddr" l) v.laddr' dq)
      (typedPointsto (structFieldRef UDPConn go!"laddr" l) v.laddr' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance UDPConn_access_store_laddr (l : Loc) (v : UDPConn) (laddr' : GoInterface) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef UDPConn go!"laddr" l) v.laddr' (DFrac.own 1))
      (typedPointsto (structFieldRef UDPConn go!"laddr" l) laddr' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with laddr' := laddr' } : UDPConn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance UDPConn_access_load_net (l : Loc) (v : UDPConn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef UDPConn go!"net" l) v.net' dq)
      (typedPointsto (structFieldRef UDPConn go!"net" l) v.net' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance UDPConn_access_store_net (l : Loc) (v : UDPConn) (net' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef UDPConn go!"net" l) v.net' (DFrac.own 1))
      (typedPointsto (structFieldRef UDPConn go!"net" l) net' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with net' := net' } : UDPConn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance UDPConn_into_val_typed :
    IntoValTypedUnderlying (GF := GF) UDPConn UDPConn.underlying := by
  solve_into_val_typed_struct

end udp

end net
end Perennial
