/-
The instances goose's proofgen emits for a translated struct (typed points-to, field access,
`IntoValTyped`), stated for the structs whose layouts are trusted in
`NetTcp/TrustedCode/net.lean` (`conn`, `TCPConn`, `TCPListener`, `OpError`), of which goose emits
none. Proved, from the hand-stated field facts `net.FieldAssumptions` (an instance hypothesis).
-/
module

public import Perennial.Proof.ProofPrelude
public import GooseLang.Ext.Tcp.Impl
public import Perennial.Golang.Theory
public import NetTcp.Code.net

@[expose] public section

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

/-! ### `conn` -/

instance conn_typed_pointsto : TypedPointsto (GF := GF) conn where
  typedPointstoDef l v dq := iprop(
    "id" ∷ typedPointsto (structFieldRef conn go!"id" l) v.id' dq ∗
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

instance TCPListener_into_val_typed :
    IntoValTypedUnderlying (GF := GF) TCPListener TCPListener.underlying := by
  solve_into_val_typed_struct

/-! ### `OpError` -/

instance OpError_typed_pointsto : TypedPointsto (GF := GF) OpError where
  typedPointstoDef l v dq := iprop(
    "Op" ∷ typedPointsto (structFieldRef OpError go!"Op" l) v.Op' dq ∗
    "Net" ∷ typedPointsto (structFieldRef OpError go!"Net" l) v.Net' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance OpError_access_load_Op (l : Loc) (v : OpError) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef OpError go!"Op" l) v.Op' dq)
      (typedPointsto (structFieldRef OpError go!"Op" l) v.Op' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance OpError_access_store_Op (l : Loc) (v : OpError) (Op' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef OpError go!"Op" l) v.Op' (DFrac.own 1))
      (typedPointsto (structFieldRef OpError go!"Op" l) Op' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with Op' := Op' } : OpError) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance OpError_access_load_Net (l : Loc) (v : OpError) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef OpError go!"Net" l) v.Net' dq)
      (typedPointsto (structFieldRef OpError go!"Net" l) v.Net' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

instance OpError_access_store_Net (l : Loc) (v : OpError) (Net' : GoString) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef OpError go!"Net" l) v.Net' (DFrac.own 1))
      (typedPointsto (structFieldRef OpError go!"Net" l) Net' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1))
      (typedPointsto l ({ v with Net' := Net' } : OpError) (DFrac.own 1)) := by
  solve_pointsto_access_struct

instance OpError_into_val_typed : IntoValTypedUnderlying (GF := GF) OpError OpError.underlying := by
  solve_into_val_typed_struct

end def_

end net
end Perennial
