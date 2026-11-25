<<<<<<< ours
||||||| base
/-
The instances goose's proofgen emits for a translated struct (typed points-to, field access,
`IntoValTyped`), stated for the structs whose layouts are trusted in
`Net/TrustedCode/net.lean` (`conn`, `TCPConn`, `TCPListener`), of which goose emits
none. Proved, from the hand-stated field facts `net.FieldAssumptions` (an instance hypothesis).
-/
=======
/-
The instances goose's proofgen emits for a translated struct (typed points-to, field access,
`IntoValTyped`), stated for the structs whose layouts are trusted in
`Net/TrustedCode/net.lean` (`conn`, `TCPConn`, `TCPListener`; `UDPConn`), of which goose emits
none. Proved, from the hand-stated field facts `net.FieldAssumptions` (`net.UdpFieldAssumptions`
for `UDPConn`; instance hypotheses).
-/
>>>>>>> theirs
module

public import Perennial.Proof.ProofPrelude
public import GooseLang.Ext.Net.Impl

@[expose] public section
<<<<<<< ours
||||||| base

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace net

open Iris Iris.BI

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-! ### `Addr`, as the trusted layouts name it -/

/-- `Addr.ty` is the named type of the trusted layouts' address fields (stated in `TrustedCode`,
which `Code.net`'s `Addr.ty` cannot be). -/
theorem Addr_ty_eq : Addr.ty = go.GoType.Named go!"net.Addr" [] := by unfold Addr.ty; rfl

instance Addr_named_underlying :
    go.UnderlyingDirectedEq (go.GoType.Named go!"net.Addr" []) Addr.underlying := by
  rw [← Addr_ty_eq]; infer_instance

/-! ### `conn` -/

instance conn_typed_pointsto : TypedPointsto (GF := GF) conn where
  typedPointstoDef l v dq := iprop(
    "id" ∷ typedPointsto (structFieldRef conn go!"id" l) v.id' dq ∗
    "laddr" ∷ typedPointsto (structFieldRef conn go!"laddr" l) v.laddr' dq ∗
    "raddr" ∷ typedPointsto (structFieldRef conn go!"raddr" l) v.raddr' dq ∗
    "net" ∷ typedPointsto (structFieldRef conn go!"net" l) v.net' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance conn_access_load_id (l : Loc) (v : conn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"id" l) v.id' dq)
      (typedPointsto (structFieldRef conn go!"id" l) v.id' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance conn_access_store_id (l : Loc) (v : conn) (id' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"id" l) v.id' (DFrac.own 1))
      (typedPointsto (structFieldRef conn go!"id" l) id' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with id' := id' } : conn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance conn_access_load_laddr (l : Loc) (v : conn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"laddr" l) v.laddr' dq)
      (typedPointsto (structFieldRef conn go!"laddr" l) v.laddr' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance conn_access_store_laddr (l : Loc) (v : conn) (laddr' : GoInterface) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"laddr" l) v.laddr' (DFrac.own 1))
      (typedPointsto (structFieldRef conn go!"laddr" l) laddr' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with laddr' := laddr' } : conn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance conn_access_load_raddr (l : Loc) (v : conn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"raddr" l) v.raddr' dq)
      (typedPointsto (structFieldRef conn go!"raddr" l) v.raddr' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance conn_access_store_raddr (l : Loc) (v : conn) (raddr' : GoInterface) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"raddr" l) v.raddr' (DFrac.own 1))
      (typedPointsto (structFieldRef conn go!"raddr" l) raddr' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with raddr' := raddr' } : conn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance conn_access_load_net (l : Loc) (v : conn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"net" l) v.net' dq)
      (typedPointsto (structFieldRef conn go!"net" l) v.net' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance conn_access_store_net (l : Loc) (v : conn) (net' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"net" l) v.net' (DFrac.own 1))
      (typedPointsto (structFieldRef conn go!"net" l) net' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with net' := net' } : conn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance conn_into_val_typed : IntoValTypedUnderlying (GF := GF) conn conn.underlying := by
  solve_into_val_typed_struct

/-! ### `TCPConn` -/

/-- `conn.ty` is the named type `TCPConn`'s embedded field has (`TCPConn.fields`, stated in
`TrustedCode`, which `Code.net`'s `conn.ty` cannot be). -/
theorem conn_ty_eq : conn.ty = go.GoType.Named go!"net.conn" [] := by unfold conn.ty; rfl

instance conn_named_underlying :
    go.UnderlyingDirectedEq (go.GoType.Named go!"net.conn" []) conn.underlying := by
  rw [← conn_ty_eq]; infer_instance

instance TCPConn_typed_pointsto : TypedPointsto (GF := GF) TCPConn where
  typedPointstoDef l v dq := iprop(
    "conn" ∷ typedPointsto (structFieldRef TCPConn go!"conn" l) v.conn' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance TCPConn_access_load_conn (l : Loc) (v : TCPConn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPConn go!"conn" l) v.conn' dq)
      (typedPointsto (structFieldRef TCPConn go!"conn" l) v.conn' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance TCPConn_access_store_conn (l : Loc) (v : TCPConn) (conn' : conn) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPConn go!"conn" l) v.conn' (DFrac.own 1))
      (typedPointsto (structFieldRef TCPConn go!"conn" l) conn' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with conn' := conn' } : TCPConn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance TCPConn_into_val_typed : IntoValTypedUnderlying (GF := GF) TCPConn TCPConn.underlying := by
  solve_into_val_typed_struct

/-! ### `TCPListener` -/

instance TCPListener_typed_pointsto : TypedPointsto (GF := GF) TCPListener where
  typedPointstoDef l v dq := iprop(
    "lid" ∷ typedPointsto (structFieldRef TCPListener go!"lid" l) v.id' dq ∗
    "addr" ∷ typedPointsto (structFieldRef TCPListener go!"addr" l) v.addr' dq ∗
    "net" ∷ typedPointsto (structFieldRef TCPListener go!"net" l) v.net' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance TCPListener_access_load_lid (l : Loc) (v : TCPListener) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPListener go!"lid" l) v.id' dq)
      (typedPointsto (structFieldRef TCPListener go!"lid" l) v.id' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance TCPListener_access_store_lid (l : Loc) (v : TCPListener) (id' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPListener go!"lid" l) v.id' (DFrac.own 1))
      (typedPointsto (structFieldRef TCPListener go!"lid" l) id' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with id' := id' } : TCPListener) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance TCPListener_access_load_addr (l : Loc) (v : TCPListener) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPListener go!"addr" l) v.addr' dq)
      (typedPointsto (structFieldRef TCPListener go!"addr" l) v.addr' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance TCPListener_access_store_addr (l : Loc) (v : TCPListener) (addr' : GoInterface) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPListener go!"addr" l) v.addr' (DFrac.own 1))
      (typedPointsto (structFieldRef TCPListener go!"addr" l) addr' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with addr' := addr' } : TCPListener) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance TCPListener_access_load_net (l : Loc) (v : TCPListener) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPListener go!"net" l) v.net' dq)
      (typedPointsto (structFieldRef TCPListener go!"net" l) v.net' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance TCPListener_access_store_net (l : Loc) (v : TCPListener) (net' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPListener go!"net" l) v.net' (DFrac.own 1))
      (typedPointsto (structFieldRef TCPListener go!"net" l) net' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with net' := net' } : TCPListener) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance TCPListener_into_val_typed :
    IntoValTypedUnderlying (GF := GF) TCPListener TCPListener.underlying := by
  solve_into_val_typed_struct

end def_

end net
end Perennial
=======

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace net

open Iris Iris.BI

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-! ### `Addr`, as the trusted layouts name it -/

/-- `Addr.ty` is the named type of the trusted layouts' address fields (stated in `TrustedCode`,
which `Code.net`'s `Addr.ty` cannot be). -/
theorem Addr_ty_eq : Addr.ty = go.GoType.Named go!"net.Addr" [] := by unfold Addr.ty; rfl

instance Addr_named_underlying :
    go.UnderlyingDirectedEq (go.GoType.Named go!"net.Addr" []) Addr.underlying := by
  rw [← Addr_ty_eq]; infer_instance

/-! ### `conn` -/

instance conn_typed_pointsto : TypedPointsto (GF := GF) conn where
  typedPointstoDef l v dq := iprop(
    "id" ∷ typedPointsto (structFieldRef conn go!"id" l) v.id' dq ∗
    "laddr" ∷ typedPointsto (structFieldRef conn go!"laddr" l) v.laddr' dq ∗
    "raddr" ∷ typedPointsto (structFieldRef conn go!"raddr" l) v.raddr' dq ∗
    "net" ∷ typedPointsto (structFieldRef conn go!"net" l) v.net' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance conn_access_load_id (l : Loc) (v : conn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"id" l) v.id' dq)
      (typedPointsto (structFieldRef conn go!"id" l) v.id' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance conn_access_store_id (l : Loc) (v : conn) (id' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"id" l) v.id' (DFrac.own 1))
      (typedPointsto (structFieldRef conn go!"id" l) id' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with id' := id' } : conn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance conn_access_load_laddr (l : Loc) (v : conn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"laddr" l) v.laddr' dq)
      (typedPointsto (structFieldRef conn go!"laddr" l) v.laddr' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance conn_access_store_laddr (l : Loc) (v : conn) (laddr' : GoInterface) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"laddr" l) v.laddr' (DFrac.own 1))
      (typedPointsto (structFieldRef conn go!"laddr" l) laddr' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with laddr' := laddr' } : conn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance conn_access_load_raddr (l : Loc) (v : conn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"raddr" l) v.raddr' dq)
      (typedPointsto (structFieldRef conn go!"raddr" l) v.raddr' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance conn_access_store_raddr (l : Loc) (v : conn) (raddr' : GoInterface) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"raddr" l) v.raddr' (DFrac.own 1))
      (typedPointsto (structFieldRef conn go!"raddr" l) raddr' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with raddr' := raddr' } : conn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance conn_access_load_net (l : Loc) (v : conn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"net" l) v.net' dq)
      (typedPointsto (structFieldRef conn go!"net" l) v.net' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance conn_access_store_net (l : Loc) (v : conn) (net' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef conn go!"net" l) v.net' (DFrac.own 1))
      (typedPointsto (structFieldRef conn go!"net" l) net' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with net' := net' } : conn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance conn_into_val_typed : IntoValTypedUnderlying (GF := GF) conn conn.underlying := by
  solve_into_val_typed_struct

/-! ### `TCPConn` -/

/-- `conn.ty` is the named type `TCPConn`'s embedded field has (`TCPConn.fields`, stated in
`TrustedCode`, which `Code.net`'s `conn.ty` cannot be). -/
theorem conn_ty_eq : conn.ty = go.GoType.Named go!"net.conn" [] := by unfold conn.ty; rfl

instance conn_named_underlying :
    go.UnderlyingDirectedEq (go.GoType.Named go!"net.conn" []) conn.underlying := by
  rw [← conn_ty_eq]; infer_instance

instance TCPConn_typed_pointsto : TypedPointsto (GF := GF) TCPConn where
  typedPointstoDef l v dq := iprop(
    "conn" ∷ typedPointsto (structFieldRef TCPConn go!"conn" l) v.conn' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance TCPConn_access_load_conn (l : Loc) (v : TCPConn) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPConn go!"conn" l) v.conn' dq)
      (typedPointsto (structFieldRef TCPConn go!"conn" l) v.conn' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance TCPConn_access_store_conn (l : Loc) (v : TCPConn) (conn' : conn) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPConn go!"conn" l) v.conn' (DFrac.own 1))
      (typedPointsto (structFieldRef TCPConn go!"conn" l) conn' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with conn' := conn' } : TCPConn) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance TCPConn_into_val_typed : IntoValTypedUnderlying (GF := GF) TCPConn TCPConn.underlying := by
  solve_into_val_typed_struct

/-! ### `TCPListener` -/

instance TCPListener_typed_pointsto : TypedPointsto (GF := GF) TCPListener where
  typedPointstoDef l v dq := iprop(
    "lid" ∷ typedPointsto (structFieldRef TCPListener go!"lid" l) v.id' dq ∗
    "addr" ∷ typedPointsto (structFieldRef TCPListener go!"addr" l) v.addr' dq ∗
    "net" ∷ typedPointsto (structFieldRef TCPListener go!"net" l) v.net' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance TCPListener_access_load_lid (l : Loc) (v : TCPListener) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPListener go!"lid" l) v.id' dq)
      (typedPointsto (structFieldRef TCPListener go!"lid" l) v.id' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance TCPListener_access_store_lid (l : Loc) (v : TCPListener) (id' : w64) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPListener go!"lid" l) v.id' (DFrac.own 1))
      (typedPointsto (structFieldRef TCPListener go!"lid" l) id' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with id' := id' } : TCPListener) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance TCPListener_access_load_addr (l : Loc) (v : TCPListener) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPListener go!"addr" l) v.addr' dq)
      (typedPointsto (structFieldRef TCPListener go!"addr" l) v.addr' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance TCPListener_access_store_addr (l : Loc) (v : TCPListener) (addr' : GoInterface) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPListener go!"addr" l) v.addr' (DFrac.own 1))
      (typedPointsto (structFieldRef TCPListener go!"addr" l) addr' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with addr' := addr' } : TCPListener) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance TCPListener_access_load_net (l : Loc) (v : TCPListener) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPListener go!"net" l) v.net' dq)
      (typedPointsto (structFieldRef TCPListener go!"net" l) v.net' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance TCPListener_access_store_net (l : Loc) (v : TCPListener) (net' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef TCPListener go!"net" l) v.net' (DFrac.own 1))
      (typedPointsto (structFieldRef TCPListener go!"net" l) net' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with net' := net' } : TCPListener) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance TCPListener_into_val_typed :
    IntoValTypedUnderlying (GF := GF) TCPListener TCPListener.underlying := by
  solve_into_val_typed_struct

/-! ### `UDPConn` (`notes/net-udp.md`), from the hand-stated `net.UdpFieldAssumptions` -/

end def_

section udp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [udp_field_sem : net.UdpFieldAssumptions]

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
>>>>>>> theirs
