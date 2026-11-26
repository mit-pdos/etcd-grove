# F9 AuthC-slot refactor: axiom-statement delta review

Branch `etcd-safe-full-authc/2026-11-26`. Commit under review: `1fc1ed7687` (HEAD). Base: `78f45712b1`
(HEAD~1). Method: the `axiom` skill. This is a delta review, so no counterexample program applies:
when the unfolded meaning of an axiom is unchanged, an attack on the new text is the same as an
attack on the old text. Each claim in `authc-scratch/axiom-deltas.md` was checked against the
sources. No build was run here. That the two `_eq` lemmas compile is the caller's targeted build;
this worktree has no `.lake`.

## Verdicts

| Axiom | Unfolds to a changed definition | Verdict |
|---|---|---|
| `etcd_dist.Serve_dist.wp_proof` | `etcdstart.memberUpOnL`, in the premise | EQUIVALENT |
| `etcd_dist.authd.Auth_UserAdd_dist.wp_proof` | `adminRepliedD`, in the post | EQUIVALENT |
| `etcd_dist.authd.Auth_RoleAdd_dist.wp_proof` | `adminRepliedD`, in the post | EQUIVALENT |
| `etcd_dist.authd.Auth_AuthEnable_dist.wp_proof` | `adminRepliedD`, in the post | EQUIVALENT |
| `etcd_dist.authd.Auth_UserGrantRole_dist.wp_proof` | `adminRepliedD`, in the post | EQUIVALENT |
| `etcd_dist.authd.Auth_RoleGrantPermission_dist.wp_proof` | `adminRepliedD`, in the post | EQUIVALENT |

No other axiom's statement changed. No other definition that an axiom reaches changed.

## 1. Why the meaning is unchanged

`Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthComp.lean:46-57`:

```lean
inductive AuthC where
  | off
  | on (γa : auth.AuthNames)
def AuthC.isOn : AuthC → Bool
  | .off => false
  | .on _ => true
```

The file is under `@[expose] public section` (line 37). The definition is a plain structural match,
so `(AuthC.on x).isOn` reduces to `true` by iota reduction for every `x`. The `def`'s body is visible
to importers, so `rfl` goes through across modules. There is only one `AuthC` in `Proof/`, `Spec/`,
`TrustedCode/` and `GooseLang/` (checked with grep), so the name cannot resolve to anything else.

- **`memberUpOnL`** (`Proof/.../etcd/dist/MemberLessor.lean:150-164`): the old body has
  `isServerReqM true …` and `isServerReadM true …`. The new body has
  `isServerReqM (AuthC.on γa).isOn …` and `isServerReadM (AuthC.on γa).isOn …` (lines 156-157).
  `γa` is the definition's own binder. Both terms reduce to `true`, so the definitions are
  definitionally equal. The binders and every other conjunct are unchanged. With the two literals
  replaced, the whitespace-normalized old body is equal to the new body (checked by script,
  `tmp/f9rev/cmp.py`).
- **`adminRepliedD`** (`Proof/.../etcd/dist/AuthViewDist.lean:171-176`): the old body has
  `adminDoneM true Γ.kv rq' L`. The new body has `adminDoneM (AuthC.on (Γ.au mid)).isOn Γ.kv rq' L`
  (line 175), where `mid` is the body's own `∃ (mid : w64)` and `Γ.au : w64 → auth.AuthNames`
  (`DistView`, `Proof/.../etcd/dist/S2Interim.lean:58`). Whatever `mid` is, the term reduces to
  `true`. The dependence on `mid` is only syntactic, so the change is not a weakening that quantifies
  over a mode. The definitions are definitionally equal.

Neither change is weaker or stronger. Each is the same proposition up to `rfl`. Polarity is
therefore irrelevant: it does not matter that `memberUpOnL` sits in `Serve_dist`'s precondition and
`adminRepliedD` in the `Auth_*_dist` posts.

## 2. The equivalence lemmas

- `etcdstart.memberUpOnL_eq` (`MemberLessor.lean:166-184`): for `b` with `hb : b = true`, it states
  `memberUpOnL s ρ E₀ lg γn id γa m γl = iprop(<body with b>)`. The proof is `subst hb; rfl`.
  Script check: with both `M true ` occurrences in the HEAD~1 body (the only `true`s there) replaced
  by `b`, the old body is token-for-token equal to the lemma's right-hand side. The binders are the
  definition's binders. The lemma sits in the same `section defsL` (lines 138-186) as the
  definition, so it has the same `variable`s and `open`s, and its right-hand side at `b := true`
  elaborates as the old body did.
- `etcd_dist.authd.adminRepliedD_eq` (`AuthViewDist.lean:179-190`): the same shape, and the same
  script check against the HEAD~1 body (one `adminDoneM true`). The binders, including
  `[NetProtoGS]`, match the definition. The lemma is in the same `section defs` (lines 116-282).

Both lemmas are correct and restate the old bodies exactly. They are not used by any proof. They
record the equivalence, and a build checks them.

## 3. Independent check for unlisted changes

- `git diff HEAD~1 HEAD --stat -- Spec TrustedCode GooseLang etc/tcb-baseline.txt` is empty. No
  `abbrev ….spec` changed, and the axiom list did not change.
- The changed files contain no `axiom` declarations. The axioms are at
  `Proof/.../dist/ServeDist.lean:74` and `Auth{UserAdd,RoleAdd,AuthEnable,UserGrantRole,RoleGrantPermission}Dist.lean:51`,
  and none of those files is in the diff.
- For every diff hunk, I listed the declaration that encloses it, in both revisions
  (`tmp/f9rev/encl.py`). Definitions whose **bodies** changed: `adminRepliedD`, `memberUpOnL` and
  `etcdstart.memberBuiltOnL` (`lib/etcdstart/Start.lean:163`). The hunks attributed to
  `writeCheckedD`, `memberBuiltL`, `authSrvTP_off`, `wp_Start_builtL`, `memberBuiltL_split` and
  `memberBuiltOnL_split` only touch the docstring of the declaration that follows. Everything else
  is a theorem. There are no `instance`, `notation` or `set_option` changes.
- Who refers to the three changed definitions (grep over `Spec/` and `Proof/`):
  - `memberUpOnL`: the only Spec reference is `Spec/.../dist/ServeDist.lean:80`. The others are
    theorems (`memberUpOnL_intro`, `wp_Start_builtOnL`, `memberUpOnL_req`) or docstrings. No `def`
    wraps it.
  - `adminRepliedD`: the only Spec references are the five `Auth_*_dist` specs
    (`AuthUserAddDist.lean:61`, `AuthUserGrantRoleDist.lean:55`, `AuthRoleAddDist.lean:53`,
    `AuthAuthEnableDist.lean:52`, `AuthRoleGrantPermissionDist.lean:57`). The other references are
    theorems (`SetupInvDist.lean`: `setupD_reply`, `setupD_reply_enable`). No `def` wraps it.
  - `memberBuiltOnL`: no Spec reference and no `def` reference. Only theorems use it
    (`memberBuiltOnL_split`, `wp_Start_builtOnL`, `MainLogger.wp_proof`). It is therefore outside
    every axiom, as the deltas file says. Its change is also by `rfl` (`true` →
    `(AuthC.on γa).isOn`).

  So the set of affected axioms is exactly the six that the deltas file lists.

- Proof-only changes (not TCB):
  - `memberUpL_req` and `memberUpOnL_req` now return `∃ on, isServerReqM on …`. Their consumers,
    `NewPeerHandler_dist.spec` (`Spec/.../NewPeerHandlerDist.lean:36`) and `PeerServe_dist.spec`
    (`PeerServeDist.lean:40`), quantify `∀ (on : Bool)`, so applying them at the existential `on`
    stays inside their claim.
  - `authSrvTPAt_off` became `authSrvTPAt_of_TP`, which nothing else refers to.
  - `MainLogger`'s `bootKVOf true` became `_`, closed with `iExactEq …; rfl`.
  - `etc/mode-allow.txt` and `etc/mode-baseline.txt` remove the F9 exception lines. These are gate
    configuration, not trusted text.

## Findings

None. The deltas file is accurate on every point I checked.
