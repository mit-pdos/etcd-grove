/-
Lean-first (no Rocq counterpart). #33 S3b W0 (2026-11-23): `s.OnDisk(n, q, more, ro, ld, ll, ch, tl, vi)`: B 290-436, `State.onDisk`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Rep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- B 290-436 `OnDisk(n, q, more, ro, ld, ll, ch, tl, vi)`: `State.onDisk`'s successor, owned, where defined, within budget (`OnDisk.Bounded`). -/
abbrev State.OnDisk.spec : Prop :=
  ∀ (p : Loc) (s : State) (n : w64) (gq : G.QItem) (q : QItem) (more : Bool) (rol : GoSlice) (ro : List Str) (ldl : GoSlice) (ld : List LeaderRec) (lll : GoSlice) (ll : TermFn (List Entry)) (chl : GoSlice) (ch : List Entry) (tll : GoSlice) (tl : TermFn Int) (vil : GoSlice) (vi : SSet) (o : Option State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check ∗
      stateRO p s ∗
      qitemRO gq q ∗
      strsRO rol ro ∗
      leadersRO ldl ld ∗
      termLogsRO lll ll ∗
      logRO chl ch ∗
      termIntsRO tll tl ∗
      strsRO vil vi ∗
      ⌜0 ≤ sint.Z n ∧ sint.Z n < s.cfg.server.length ∧ OnDisk.Bounded { s, n := sint.nat n, q, more, ro, ld, ll, ch, tl, vi } ∧
        s.onDisk (sint.nat n) q more ro ld ll ch tl vi = .ok o⌝ }}
    (App (App (App (App (App (App (App (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State.ty @!! go!"OnDisk")) (Val #n)) (Val #gq)) (Val #more)) (Val #rol)) (Val #ldl)) (Val #lll)) (Val #chl)) (Val #tll)) (Val #vil))
  {{ (q' : Loc) (ok : Bool), RET (PairV #q' #ok); succOwn q' ok o }}

end spec

end AntCheck
end EtcdGrove
end Perennial
