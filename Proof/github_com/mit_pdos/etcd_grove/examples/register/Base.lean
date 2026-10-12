/-
Lean-first (no Rocq counterpart).

# The register: package initialization and the pure model (2026-10-10)

`examples/register/register.go` has no package-level variable (`opPut`, `opGet` and
`maxIndex` are constants), so its package fact is `True`; the packages it imports have
theirs (Perennial's `context`, `encoding/binary`, `sync`; etcd-grove's raft and `raftpb`,
`Proof/go_etcd_io/raft/v3/Base.lean`).

The pure model: an operation's encoding (`encodeOp`: the proposing replica and its
sequence number, little-endian, the kind, the value), what `decode` reads back
(`decodeOp`), and the register's state machine over the client log (`regFold`: a `Put`
sets the value, anything else -- a `Get`, a datum that is no operation -- leaves it).
The client log holds each operation once (`firstOcc`, `Protocol/Model.lean`), which is
what `apply`'s table of applied encodings (`AppliedOk`) mirrors.
-/
module

public import Proof.go_etcd_io.raft.v3.Link
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.register
public import Perennial.Proof.encoding.binary

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.mit_pdos.etcd_grove.examples.register

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.register

namespace EtcdGrove

/-! ## The pure model -/

/-- `opPut`. -/
def opPutB : w8 := W8 1

/-- What `encode(replica, seq, kind, val)` returns. -/
def encodeOp (replica seq : w64) (kind : w8) (val : List w8) : List w8 :=
  u64Le replica ++ u64Le seq ++ [kind] ++ val

/-- What `decode` reads back: `none` for fewer than 17 bytes. -/
def decodeOp (d : List w8) : Option (w64 × w64 × w8 × List w8) :=
  if 17 ≤ d.length then
    some (leToU64 (d.take 8), leToU64 ((d.drop 8).take 8), d.getD 16 (W8 0), d.drop 17)
  else none

/-- An operation's key: its replica and sequence number. -/
def opKey (d : List w8) : Option (w64 × w64) :=
  (decodeOp d).map (fun x => (x.1, x.2.1))

/-- One datum of the client log applied to the value. -/
def regApply (x : List w8) (d : List w8) : List w8 :=
  match decodeOp d with
  | some (_, _, k, v) => if k = opPutB then v else x
  | none => x

/-- The register's value after the client log `L`. -/
def regFold (L : List (List w8)) : List w8 := L.foldl regApply []

/-- The value after an operation of kind `kind` with value `val` on `x`. -/
def opNext (kind : w8) (val x : List w8) : List w8 := if kind = opPutB then val else x

/-- `apply`'s table: the decodable data of the client log `L`, each mapped to `true`. -/
def AppliedOk (A : GMap (List w8) Bool) (L : List (List w8)) : Prop :=
  ∀ d, A !! d = if d ∈ L ∧ (decodeOp d).isSome then some true else none

theorem encodeOp_length (replica seq : w64) (kind : w8) (val : List w8) :
    (encodeOp replica seq kind val).length = 17 + val.length := by
  simp [encodeOp, u64Le_length]; omega

theorem decodeOp_encodeOp (replica seq : w64) (kind : w8) (val : List w8) :
    decodeOp (encodeOp replica seq kind val) = some (replica, seq, kind, val) := by
  unfold decodeOp
  rw [ite_eq_left (by rw [encodeOp_length]; omega)]
  have h1 : (encodeOp replica seq kind val).take 8 = u64Le replica := by
    simp [encodeOp, u64Le_length]
  have h2 : ((encodeOp replica seq kind val).drop 8).take 8 = u64Le seq := by
    simp [encodeOp, u64Le_length]
  have h3 : (encodeOp replica seq kind val).getD 16 (W8 0) = kind := by
    simp [encodeOp, List.getD_eq_getElem?_getD, List.getElem?_append_right, u64Le_length]
  have h4 : (encodeOp replica seq kind val).drop 17 = val := by
    have hr := u64Le_length replica
    have hs := u64Le_length seq
    simp only [encodeOp, List.append_assoc, List.singleton_append]
    rw [show 17 = (u64Le replica).length + ((u64Le seq).length + 1) by omega,
      List.drop_append, List.drop_append]
    rfl
  rw [h1, h2, h3, h4, u64Le_to_word, u64Le_to_word]

theorem opKey_encodeOp (replica seq : w64) (kind : w8) (val : List w8) :
    opKey (encodeOp replica seq kind val) = some (replica, seq) := by
  simp [opKey, decodeOp_encodeOp]

theorem regFold_snoc (L : List (List w8)) (d : List w8) :
    regFold (L ++ [d]) = regApply (regFold L) d := by
  simp [regFold, List.foldl_append]

theorem regApply_encodeOp (x : List w8) (replica seq : w64) (kind : w8) (val : List w8) :
    regApply x (encodeOp replica seq kind val) = opNext kind val x := by
  simp [regApply, decodeOp_encodeOp, opNext]

theorem regApply_none (x d : List w8) (h : decodeOp d = none) : regApply x d = x := by
  simp [regApply, h]

end EtcdGrove

end Perennial
