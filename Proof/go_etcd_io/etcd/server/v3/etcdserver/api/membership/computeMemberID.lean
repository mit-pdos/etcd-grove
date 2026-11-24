/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/computeMemberID.lean`: the URL strings
(`StringSlice`, one URL), `sort.Strings` (one string), `strings.Join` (the string), the token appended,
`sha1.Sum`, `binary.BigEndian.Uint64` of its first 8 bytes. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.computeMemberID
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.URLs__StringSlicePlain
public import Spec.encoding.binary.bigEndian__Uint64
public import Perennial.Spec.sort.Strings
public import Perennial.Spec.strings.Join
public import Perennial.Spec.crypto.sha1.Sum

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

/-- `binary.BigEndian.Uint64` of 8 bytes is their big-endian value, `memberIdOf`'s fold. -/
theorem beToU64_eq_fold (bs : List w8) :
    beToU64 bs = W64 (bs.foldl (fun acc b => acc * 256 + b.toNat) 0) := by
  unfold beToU64
  rw [leToU64_unseal]
  unfold leToU64Def
  have h : ∀ l : List w8, LittleEndian.combine l.reverse = l.foldl (fun acc b => acc * 256 + b.toNat) 0 := by
    intro l
    induction l using List.reverseRecOn with
    | nil => rfl
    | append_singleton l b ih =>
      rw [List.reverse_append, List.foldl_append, ← ih]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
        LittleEndian.combine, List.foldl_cons, List.foldl_nil]
      omega
  rw [h]
  apply BitVec.eq_of_toNat_eq
  simp

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

theorem membership.computeMemberID.wp_proof
    [go_etcd_io.etcd.client.pkg.v3.types.Assumptions] [_root_.Perennial.sort.Assumptions]
    [_root_.Perennial.strings.Assumptions] [_root_.Perennial.crypto.sha1.Assumptions]
    [encoding.binary.Assumptions]
    (hSS : types.URLs.StringSlicePlain.spec (GF := GF) (hG := hG))
    (hSort : _root_.Perennial.sort.Strings.spec (GF := GF) (hG := hG))
    (hJoin : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG))
    (hSum : _root_.Perennial.crypto.sha1.Sum.spec (GF := GF) (hG := hG))
    (hU64 : binary.bigEndian.Uint64.spec (GF := GF) (hG := hG)) :
    membership.computeMemberID.spec (GF := GF) (hG := hG) := by
  intro sl u token hfips
  wp_start as #Hsl
  wp_auto
  skip

end proof

end EtcdGrove
end Perennial
