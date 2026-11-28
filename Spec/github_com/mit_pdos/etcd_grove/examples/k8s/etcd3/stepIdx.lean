/-
Lean-first (no Rocq counterpart).

# `stepIdx(memo, c, in, out)` (k8s-dist K9 step 3, `notes/k8s-dist-k9.md`)

`step`'s spec, over the memo `memo` (`memoOwn`), with a watch's history well formed (`HWf`: what
makes the memo's verdict, kept per history node, the one `watchOkIdx` returns).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WMemo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.k8s.etcd3


section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- See the file header. -/
abbrev stepIdx.spec : Prop :=
  ∀ (memo : Loc) (c : mcfg) (g : GCfg) (x : Input) (y : Output),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ memoOwn memo ∗ cfgOwn c g ∗ ⌜g.st.st.items.length + 1 < 2 ^ 63 ∧ g.pend.length + 1 < 2 ^ 63 ∧
        g.st.hist.length + 1 < 2 ^ 64 ∧
        (x.Kind' = W64 5 → uint.Z g.st.st.rv < 2 ^ 63 ∧
          ∀ n, parseRVD x.MinRV' = some n → uint.Z n < 2 ^ 63) ∧
        (x.Kind' = W64 5 → HWf g.st)⌝ }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.stepIdx)) (Val #memo)) (Val #c)) (Val #x)) (Val #y))
  {{ (r : GoSlice) (cs : List mcfg), RET #r;
      r ↦* cs ∗ [∗list] c';g' ∈ cs;stepL g x (plainOut y), cfgOwn c' g' }}

end spec

end k8s_etcd3
end EtcdGrove
end Perennial
