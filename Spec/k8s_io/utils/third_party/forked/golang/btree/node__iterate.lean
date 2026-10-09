module
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Defs
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Model
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI k8s_io.utils.third_party.forked.golang.btree

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- `(*node[T]).iterate(dir, start, stop, includeStart, hit, iter)`: call `iter` on the
subtree's entries in the range, in order (`ascend`, `dir = 1`) or in reverse
(`descend`, `dir = -1`), until `iter` returns false or an entry passes `stop`;
`ok` (the second result) is whether to go on.

The subtree's entries in range, `seg`, continue an iteration over `r` that has visited
`acc`. Every caller with a `start` has `includeStart`, and only `descend` reads `hit`
(whether an entry was visited already: then none of this subtree has `start`'s key);
it comes back true exactly if some entry has been visited. -/
abbrev node.iterate.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {T : go.GoType}
    [IntoValTyped (GF := GF) V T] {K : Type} (o : ItemOrder GF V K) (c f : Loc) (less : GoFunc) (dq : DFrac) (n : Loc) (t : Tree (V × K))
    (dir : w64) (start stop : optionalItem V) (ks ku : Option K) (includeStart hit : Bool)
    (iter : GoFunc) (r acc : List (V × K)) (I : List (V × K) → Bool → IProp GF) (d h : Nat),
  t.Shape d h → Sorted o.lt t.elems → (dir = W64 1 ∨ dir = W64 (-1)) →
  (start.valid' = true → includeStart = true) →
  (dir = W64 (-1) → hit = true → ∀ a, ks = some a → ∀ e ∈ t.elems, o.lt e.2 a) →
  let seg := if dir = W64 1 then ascRange o.lt t.elems ks ku else descRange o.lt t.elems ks ku
  (acc ++ seg) <+: r →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗ isCow o c f less ∗ ownNode o c f less dq n t ∗ allItems o t.elems ∗
      optKey o start ks ∗ optKey o stop ku ∗ iterProtocol o iter r I ∗ I acc false }}
    (App (App (App (App (App (App (Val (n @!! go.GoType.PointerType (node.ty T) @!! go!"iterate")) (Val #dir)) (Val #start)) (Val #stop)) (Val #includeStart)) (Val #hit)) (Val #iter))
  {{ (hit' ok : Bool), RET (PairV #hit' #ok);
      ownNode o c f less dq n t ∗
      ((⌜ok = true ∧ (dir = W64 (-1) → hit' = (hit || !seg.isEmpty))⌝ ∗ I (acc ++ seg) false) ∨
       (⌜ok = false⌝ ∗
        ((∃ pre, ⌜acc <+: pre ∧ pre <+: acc ++ seg⌝ ∗ I pre true) ∨
         (I (acc ++ seg) false ∗
          ⌜∃ b, ku = some b ∧ ∃ e ∈ t.elems,
            if dir = W64 1 then ¬ o.lt e.2 b else ¬ o.lt b e.2⌝)))) }}

end spec

end btree
end EtcdGrove
end Perennial
