module
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Write
public import Proof.go_etcd_io.bbolt.internal.common.Bytes
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Copy

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]
-- `hash.Hash64`'s type (its underlying interface): `internal/common` reaches `hash` only
-- through `hash/fnv`, so its `Assumptions` do not include `hash`'s
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem Meta.Write.wp_proof (hSum : Meta.Sum64.spec (GF := GF) (hG := hG))
    (hSet : Page.SetFlags.spec (GF := GF) (hG := hG))
    (hMeta : Page.Meta.spec (GF := GF) (hG := hG))
    (hCopy : Meta.Copy.spec (GF := GF) (hG := hG)) :
    Meta.Write.spec (GF := GF) (hG := hG) := by
  intro l p v pg w Hc Hroot Hfl
  wp_start as ⟨Hl, Hp, Hm⟩
  wp_auto
  rw [decide_eq_false (by word)]
  try wp_auto
  rcases Hfl with Hlt | Heq
  · rw [decide_eq_false (by word)]
    try wp_auto
    wp_apply hSet $$ [$Hp] as Hp
    try wp_auto
    wp_apply hSum l v (DFrac.own 1) Hc $$ [$Hl] as Hl
    try wp_auto
    wp_apply hMeta
    try wp_auto
    wp_apply hCopy $$ [$Hl $Hm] as ⟨Hl, Hm⟩
    try wp_auto
    iapply HΦ; iframe
  · by_cases Hle : uint.Z v.pgid' ≤ uint.Z v.freelist'
    · rw [decide_eq_true Hle]
      try wp_auto
      rw [decide_eq_true Heq]
      try wp_auto
      wp_apply hSet $$ [$Hp] as Hp
      try wp_auto
      wp_apply hSum l v (DFrac.own 1) Hc $$ [$Hl] as Hl
      try wp_auto
      wp_apply hMeta
      try wp_auto
      wp_apply hCopy $$ [$Hl $Hm] as ⟨Hl, Hm⟩
      try wp_auto
      iapply HΦ; iframe
    · rw [decide_eq_false Hle]
      try wp_auto
      wp_apply hSet $$ [$Hp] as Hp
      try wp_auto
      wp_apply hSum l v (DFrac.own 1) Hc $$ [$Hl] as Hl
      try wp_auto
      wp_apply hMeta
      try wp_auto
      wp_apply hCopy $$ [$Hl $Hm] as ⟨Hl, Hm⟩
      try wp_auto
      iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
