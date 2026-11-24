/-
**etcd's unary interceptor chain, by identity** (2026-11-24, `notes/axiom-review/norefusal-link.md`):
which `GoFunc`s `v3rpc.Server(s, ...)` chains, so that the members' axiom (`etcd_noRefusal`) can say
"the server at the address runs etcd's chain over `s`", not just "a chain meeting etcd's contracts" (a
refusing interceptor meets `srvInterceptorOk`). Lean-first (no Rocq counterpart).

`newLogUnaryInterceptor(s)` and `newUnaryInterceptor(s)` copy `s` into a fresh variable `l` and return
the closure `func(ctx, req, info, handler) {...}` over it: the value is the closure of their code with
`s` bound to `l` (`v3rpc.icClosureOf`, read off the translated code, `Code/.../v3rpc.lean`), and `l`
holds `s` for good (`l ↦□ s`); their proofs return both. grpc-prometheus's interceptor is named by its
trusted spec (`promUnaryIc`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota
public import Proof.github_com.grpc_ecosystem.go_grpc_middleware.providers.prometheus.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The closure a constructor of the shape `func(s) F { s := s; return func(ctx, ...) {...} }`
returns, its `s` the variable `l`**: for the translation `LamV "s" (Let "$res0" _ (Seq (exceptionDo
(Let "s" _ (Let "$r0" (Rec f x body) _))) _))`, the closure `⟨f, x, body[s := l]⟩` (the `Let "s"` binds
the copy's address, which the closure reads `s` through); `func.nil` for any other shape. -/
def v3rpc.icClosureOf (impl : val) (l : Loc) : GoFunc :=
  match impl with
  | .RecV _ _ (.App (.Rec _ _ (.App (.Rec _ _ _)
      (.App _ (.App (.Rec _ _ (.App (.Rec _ _ _) (.Rec f x body))) _)))) _) =>
      func.mk f x (subst "s" #l body)
  | _ => func.nil

/-- **`ic` is `newLogUnaryInterceptor(s)`'s closure** (persistent): its code over a variable holding
`s` for good. -/
def v3rpc.isLogUnaryIc (ic : GoFunc) (s : Loc) : IProp GF :=
  iprop(∃ l : Loc, ⌜ic = v3rpc.icClosureOf
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newLogUnaryInterceptor.impl l⌝ ∗ l ↦□ s)

/-- **`ic` is `newUnaryInterceptor(s)`'s closure** (persistent): its code over a variable holding `s`
for good. -/
def v3rpc.isUnaryIc (ic : GoFunc) (s : Loc) : IProp GF :=
  iprop(∃ l : Loc, ⌜ic = v3rpc.icClosureOf
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newUnaryInterceptor.impl l⌝ ∗ l ↦□ s)

/-- **`ics` is etcd's unary chain over `s`** (persistent): `v3rpc.Server(s, nil, nil, ...)`'s, the log
interceptor, grpc-prometheus's and etcd's own, in that order and nothing else. -/
def v3rpc.etcdUnaryIcs (s : Loc) (ics : List GoFunc) : IProp GF :=
  iprop(∃ il im iu : GoFunc, ⌜ics = [il, im, iu] ∧ promUnaryIc im⌝ ∗
    v3rpc.isLogUnaryIc il s ∗ v3rpc.isUnaryIc iu s)

instance v3rpc.isLogUnaryIc_persistent (ic : GoFunc) (s : Loc) :
    Persistent (v3rpc.isLogUnaryIc (GF := GF) ic s) := by
  unfold v3rpc.isLogUnaryIc; infer_instance

instance v3rpc.isUnaryIc_persistent (ic : GoFunc) (s : Loc) :
    Persistent (v3rpc.isUnaryIc (GF := GF) ic s) := by
  unfold v3rpc.isUnaryIc; infer_instance

instance v3rpc.etcdUnaryIcs_persistent (s : Loc) (ics : List GoFunc) :
    Persistent (v3rpc.etcdUnaryIcs (GF := GF) s ics) := by
  unfold v3rpc.etcdUnaryIcs; infer_instance

/-- `etcdUnaryIcs` from its three pieces. -/
theorem v3rpc.etcdUnaryIcs_intro (s : Loc) (il im iu : GoFunc) (him : promUnaryIc im) :
    v3rpc.isLogUnaryIc (GF := GF) il s ∗ v3rpc.isUnaryIc iu s ⊢ v3rpc.etcdUnaryIcs s [il, im, iu] := by
  iintro ⟨#Hl, #Hu⟩
  unfold v3rpc.etcdUnaryIcs
  iexists il, im, iu
  iframe #
  ipureintro; exact ⟨rfl, him⟩

end defs

end EtcdGrove
end Perennial
