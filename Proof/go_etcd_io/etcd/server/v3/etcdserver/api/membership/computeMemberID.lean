/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/computeMemberID.lean` (claim #34,
stage 2, 2026-11-25). Lean-first. The URLs' strings (`StringSlice`, plain), sorted (`sort.Strings`:
`mergeSort strLeB`, `sortStrings_eq`), joined with `""` (`flatten`), the token appended, hashed
(`crypto/sha1.Sum`), and the first eight bytes of the digest decoded big-endian.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.computeMemberID
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.MemberIDLemmas
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.URLs__StringSlice
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

/-- SHA-1's digest has 20 bytes. -/
theorem membership.sha1_length (m : List w8) : (crypto.sha1.sha1 m).length = 20 := by
  unfold crypto.sha1.sha1
  simp [crypto.sha1.bytes32]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.computeMemberID.wp_proof
    (hSS : types.URLs.StringSlice.specP (GF := GF) (hG := hG))
    (hSort : sort.Strings.spec (GF := GF) (hG := hG))
    (hJoin : strings.Join.spec (GF := GF) (hG := hG))
    (hSum : crypto.sha1.Sum.spec (GF := GF) (hG := hG))
    (hU64 : binary.bigEndian.Uint64.spec (GF := GF) (hG := hG)) :
    membership.computeMemberID.spec (GF := GF) (hG := hG) := by
  intro sl us token Hfips Hplain Hlen
  wp_start as #Hus
  wp_auto
  ihave #Htpk : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types $$ []
  · iPkgInit
  ihave #Hspk : isPkgInit (PROP := IProp GF) pkg_id.sort $$ []
  · iPkgInit
  ihave #Hstpk : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  ihave #Hhpk : isPkgInit (PROP := IProp GF) pkg_id.crypto.sha1 $$ []
  · iPkgInit
  ihave #Hbpk : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
  · iPkgInit
  -- `peerURLs.StringSlice()`
  wp_apply (hSS peerURLs_ptr (DFrac.own 1) sl us Hplain) $$ [peerURLs] as %out ⟨-, Hout⟩
  · iframe #; iframe peerURLs
  (try wp_auto)
  -- `sort.Strings(peerURLstrs)`
  wp_apply (hSort out (us.map fun u => go!"http://" ++ u.Host')) $$ [Hout] as %xs' ⟨Hout, %Hperm, %Hsorted⟩
  · iframe #; iframe Hout; ipureintro; simp only [List.length_map]; omega
  (try wp_auto)
  have hxs' := membership.sortStrings_eq _ _ Hperm Hsorted
  -- `strings.Join(peerURLstrs, "")`
  wp_apply (hJoin out xs' (DFrac.own 1) go!"") $$ [Hout] as Hout
  · iframe #; iframe Hout
  (try wp_auto)
  -- `[]byte(joinedPeerUrls)`, `append(b, []byte(clusterName)...)`
  wp_apply wp_string_to_bytes as %bs ⟨Hbs, Hbcap⟩
  (try wp_auto)
  wp_apply wp_string_to_bytes as %ts ⟨Hts, -⟩
  (try wp_auto)
  wp_apply (wp_slice_append (V := w8)) $$ [Hbs Hbcap Hts] as %bs2 ⟨Hbs2, -, -⟩
  · iframe
  (try wp_auto)
  -- `sha1.Sum(b)`
  wp_apply (hSum bs2 (DFrac.own 1) _ Hfips) $$ [Hbs2] as Hbs2
  · iframe #; iframe Hbs2
  (try wp_auto)
  -- `binary.BigEndian.Uint64(hash[:8])`
  ihave Hsl := slice_array (GF := GF) hash_ptr _ _ (by simp [membership.sha1_length]) $$ hash
  icases (ownSlice_slice (V := w8) (W64 0) (W64 8) _ _ _
    ⟨by decide, by decide, by simp; decide⟩).1 $$ Hsl with ⟨-, Hmid, -⟩
  have hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 8))
      (crypto.sha1.sha1 (([] : GoString).intercalate xs' ++ token)) =
      (crypto.sha1.sha1 (([] : GoString).intercalate xs' ++ token)).take 8 ++ [] := by
    simp only [subslice, List.append_nil]
    rfl
  ihave Hmid' : (slice.slice (slice.mk hash_ptr (W64 20) (W64 20)) w8 (W64 0) (W64 8) ↦*
      ((crypto.sha1.sha1 (([] : GoString).intercalate xs' ++ token)).take 8 ++ []) : IProp GF) $$ [Hmid]
  · rw [← hsub]; iexact Hmid
  wp_apply (hU64 _ ((crypto.sha1.sha1 (([] : GoString).intercalate xs' ++ token)).take 8) []
    (DFrac.own 1) (by simp [membership.sha1_length])) $$ [Hmid'] as Hmid
  · iframe #; iframe Hmid'
  (try wp_auto)
  have hid : beToU64 ((crypto.sha1.sha1 (([] : GoString).intercalate xs' ++ token)).take 8) =
      membership.memberIDOf (us.map membership.urlStrOf) token := by
    rw [membership.intercalate_empty, hxs']
    rfl
  rw [hid]
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
