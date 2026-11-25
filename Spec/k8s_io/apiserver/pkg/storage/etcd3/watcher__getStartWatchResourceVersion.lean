/-
`(*watcher).getStartWatchResourceVersion(ctx, rev, opts)` (`k8s.io/apiserver/pkg/storage/etcd3/
watcher.go:194-218`), with `WatchList` on (`watchListOn`) and `SendInitialEvents` read as `sie`: a
positive `rev` itself; `0` when initial events are asked or left unset; otherwise (a watch from "now",
`SendInitialEvents = false` at `rev ≤ 0`) the result of `w.getCurrentStorageRV(ctx)`, whose call the
caller describes by the WP `Hcrv` with a post `R` (the store's: `GetCurrentResourceVersion`): its
error if it fails (with `0`), else its revision read as an `int64`. Proved (k8s 7f-5a-P step 3).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev watcher.getStartWatchResourceVersion.spec : Prop :=
  ∀ (wp : Loc) (crv : GoFunc) (ctx : GoInterface) (rev : w64)
    (opts : k8s_io.apiserver.pkg.storage.ListOptions) (sie : Option Bool)
    (R : w64 → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ levelTok 0 ∗ (structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watcher go!"getCurrentStorageRV" wp ↦□ crv ∗
      sendInitIs opts.SendInitialEvents' sie ∗ watchListOn ∗
      (⌜sint.Z rev ≤ 0 ∧ sie = some false⌝ -∗ levelTok 0 -∗
        WP (App (Val #crv) (Val #ctx)) {{ v, levelTok 0 ∗ ∃ (n : w64) (err : GoInterface),
          ⌜v = PairV #n #err⌝ ∗ R n err }})) }}
    (App (App (App (Val (wp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watcher.ty @!!
      go!"getStartWatchResourceVersion")) (Val #ctx)) (Val #rev)) (Val #opts))
  {{ (r : w64) (err : GoInterface), RET (PairV #r #err); levelTok 0 ∗ (if 0 < sint.Z rev then ⌜r = rev ∧ err = GoInterface.nil⌝
      else if sie = some false then
        ∃ n : w64, R n err ∗ ⌜r = if err = GoInterface.nil then n else W64 0⌝
      else ⌜r = W64 0 ∧ err = GoInterface.nil⌝) }}

end spec

end k8s
end EtcdGrove
end Perennial
